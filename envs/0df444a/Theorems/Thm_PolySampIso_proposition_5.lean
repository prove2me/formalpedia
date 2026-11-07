-- Prove2me | Theorems.Thm_PolySampIso_proposition_5
-- name    : PolySampIso.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:47.512459+00:00
-- url     : https://prove2.me/theorems/24f232e2-2a46-46cd-bb36-b1e3bc73b91f
-- title:
--   Proposition 5, p.34 — AnalyticCenter: ‖∇ψ(x̂)‖_{x̂,∗} ≤ ∆ in time O(mn^{ω−1}(√m log(mR/r) + log log(1/∆)))
-- statement:
--   For every $\varepsilon>0$ there are a program for the real RAM and a constant $C>0$ with the following property. Let $X=\{Ax<b\}\subseteq\mathbb R^n$ be a polytope with $m$ constraints, $0<r<R$, $\Delta\in(0,\tfrac12)$, and $x_0$ a point with $B_2(x_0,r)\subset X\subset B_2(x_0,R)$. On input $\Delta,r,R,x_0,A,b$ the program halts after at most
--
--   $$C\,m\,n^{\omega-1+\varepsilon}\Big(\sqrt m\log\frac{mR}r+\log\log\frac1\Delta\Big)$$
--
--   operations and outputs a point $\hat x\in X$ with $\|\nabla\psi(\hat x)\|_{\hat x,*}\le\Delta$, where $\psi$ is the log barrier.
--
--   An approximate analytic center is what Phase 1 of Algorithm 5 needs to place its Gaussian; its cost is the second term of Theorem 2, which depends on the aspect ratio $R/r$ only logarithmically.
--
--   Differences from the source:
--   - reading: There is an algorithm, AnalyticCenter(X, ∆), … runs in time O(mn^{ω−1}(…)) (in the real RAM of §2.1) → ∀ ε > 0 ∃ one Admissible program of PolySampIso.Machine and C > 0, before all inputs, halting on every pair of streams with work ≤ C·m·n^{ω−1+ε}(√m log(mR/r) + log log(1/∆)) and output x̂ ∈ X with ‖∇ψ(x̂)‖_{x̂,∗} ≤ ∆; reason: the paper names the model without an instruction list; ω is an infimum that need not be attained
--   - encoding: B2(x0, r) ⊂ X ⊂ B2(x0, R) → open inner ball, closed outer ball; reason: the weakest choices; for the open X they are equivalent to the other choices up to the strictness of R
--   - encoding: ∇ψ(x̂) → A⊤s(x̂)⁻¹; reason: the paper's formula for ∇ψ (p.10)
--   - encoding: X a bounded polytope, n implicit → n ≥ 1; boundedness and nonemptiness follow from the two containments; reason: the hypotheses imply it
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 5, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Proposition 5** (AnalyticCenter: an approximate analytic center in
`O(mn^{ω−1}(√m log(mR/r) + log log(1/∆)))` time).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 5, p.34 (PDF p.36):

"Proposition 5. Let X be a bounded polytope induced by (A, b), let 0 < r < R, and let ∆ ∈ (0, 1/2).
There is an algorithm, AnalyticCenter(X, ∆), that if given x0 ∈ X with B2(x0, r) ⊂ X ⊂ B2(x0, R),
outputs a point x̂ with ∥∇ψ(x̂)∥x̂,∗ ≤ ∆, following the notation of Section 2.3. Moreover, the
algorithm runs in time O(mn^{ω−1}(√m log(mR/r) + log log(1/∆)))."

**Formalization Note.** In the machine `PolySampIso.Machine`, for every `ε > 0` one `Admissible`
program and one constant `C`, chosen before all inputs. The input is `∆, r, R` in cells `0, 1, 2`,
then `x₀`, `A`, `b` (`inputState`). On every pair of streams the run halts with work
`≤ C·m·n^{ω−1+ε}(√m log(mR/r) + log log(1/∆))` and the halted output `x̂` lies in `X` and satisfies
`‖∇ψ(x̂)‖_{x̂,∗} ≤ ∆` (`∇ψ = A⊤s⁻¹`, `‖·‖_{x̂,∗}` the dual local norm (8)). `ω` is read with `ε` as in
Theorem 2. The balls are the open inner and closed outer ball; they make `X` bounded and nonempty
(`m ≥ n + 1 ≥ 2`), so the bracket is positive. -/
theorem proposition_5 :
    ∀ ε : ℝ, 0 < ε → ∃ P : Program, Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
        (r R Δ : ℝ), 0 < n → 0 < r → r < R → 0 < Δ → Δ < 1 / 2 →
        Metric.ball x₀ r ⊆ polytope A b → polytope A b ⊆ Metric.closedBall x₀ R →
        let ω := OAI.MatrixMultiplication.Arithmetic.omega ℝ
        let s₀ := inputState ![Δ, r, R] x₀ A b []
        ∀ ωs : Streams, ∃ k, (run P s₀ ωs k).halted = true ∧
          ((run P s₀ ωs k).work : ℝ) ≤ C * m * (n : ℝ) ^ (ω - 1 + ε) *
            (Real.sqrt m * Real.log (m * R / r) + Real.log (Real.log (1 / Δ))) ∧
          output n (run P s₀ ωs k) ∈ polytope A b ∧
          dualLocalNorm A b (output n (run P s₀ ωs k))
            (gradLogBarrier A b (output n (run P s₀ ωs k))) ≤ Δ := by sorry

end PolySampIso
