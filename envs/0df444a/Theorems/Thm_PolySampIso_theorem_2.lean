-- Prove2me | Theorems.Thm_PolySampIso_theorem_2
-- name    : PolySampIso.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:57.250823+00:00
-- url     : https://prove2.me/theorems/c444ac60-97a2-4a32-8d1a-92c496e7b8bc
-- title:
--   Theorem 2, p.3 — PTERRYS samples π to TV δ in time O(m²n^{ω−1}log³(m/δ) + m^{3/2}n^{ω−1}log(mR log(1/δ)/r))
-- statement:
--   Let $\omega$ be the exponent of square matrix multiplication. For every $\varepsilon>0$ there are a program for the real RAM with one-dimensional Gaussian and exponential samples and a constant $C>0$ with the following property. Let $m,n\ge1$, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $X=\{x\in\mathbb R^n:Ax<b\}$ and $\pi$ the uniform distribution on $X$; let $0<r<R$, $\delta\in(0,\tfrac12)$, and $x_0$ a point with $B_2(x_0,r)\subset X\subset B_2(x_0,R)$. On input $\delta,r,R,x_0,A,b$:
--
--   1. on every realization of its randomness the program halts after at most
--   $$C\Big(m^2n^{\omega-1+\varepsilon}\log^3\frac m\delta+m^{3/2}n^{\omega-1+\varepsilon}\log\frac{mR\log(1/\delta)}r\Big)$$
--   operations;
--   2. its output $x\in\mathbb R^n$ is a measurable function of the randomness;
--   3. $\mathrm{TV}(\mathrm{Law}(x),\pi)\le\delta$.
--
--   The paper's algorithm is PTERRYS (Algorithm 8): the functional cooling scheme (Algorithm 5) with the dual-conditioned proximal sampler (Algorithm 7) at step size $\tau=\lceil C\log(m/\delta)\rceil$. Its iteration count, $m$ times polylogarithmic factors, matches the $1/(16m)$ log-barrier Poincaré constant of $\pi$ (Lemma 3), each iteration costing $\tilde O(mn^{\omega-1})$; for $m=O(n)$ this improves the previous best polytope samplers by a factor of at least $n^{2/3}$, with no warm start.
--
--   **Formalization Note** The machine is `PolySampIso.Machine`; one admissible program serves every input. $\omega$ is `OAI.MatrixMultiplication.Arithmetic.omega ℝ`, and the time bound is read with $n^{\omega-1+\varepsilon}$ for every $\varepsilon>0$, since the infimum need not be attained. All logarithms are natural.
--
--   Differences from the source:
--   - reading: PTERRYS (Algorithm 8), or Algorithm 5, using Algorithm 7 as O with τ = ⌈C log(m/δ)⌉ for a universal constant C > 0 → ∃ one Admissible program P of PolySampIso.Machine and C > 0; reason: Algorithm 8 calls AnalyticCenter, which the paper gives only as an existence statement (Proposition 5); the abstract states the result as 'an algorithm'
--   - reading: the real RAM model, scalar operations in O(1) time, sample access to one-dimensional Gaussian and exponential distributions in O(1) time (§2.1) → PolySampIso.Machine: the SmaleNinth real-RAM core with rational literals, √, exp, log, N(0,1) and Exp(1) draws, unit cost per instruction; reason: the paper names the model without an instruction list
--   - reading: time O(m²n^{ω−1}log³(m/δ) + m^{3/2}n^{ω−1}log(mR log(1/δ)/r)) → ∀ ε > 0 (before the program), work ≤ C(m²n^{ω−1+ε}log³(m/δ) + m^{3/2}n^{ω−1+ε}log(mR log(1/δ)/r)); reason: ω = OAI…omega ℝ is an infimum that need not be attained
--   - reading: it runs in time … → the work bound holds on every pair of random streams; reason: every loop of Algorithms 5–8 has a deterministic length; the worst-case reading is the stronger one
--   - encoding: TV(Law(x), π) ≤ δ → the output map is measurable and |P(x ∈ B) − π(B)| ≤ δ for every measurable B; reason: the sup form equals ½∫|dµ − dν| for probability measures; measurability makes Law(x) defined
--   - encoding: B2(x0, r) ⊂ X ⊂ B2(x0, R) → the open inner ball and the closed outer ball; reason: the weakest choices; they imply that X is nonempty, full-dimensional and bounded and that A has full column rank
--   - reading: the correctness clause, stated before 'Moreover, if the algorithm is given x0 …' → all clauses are stated for inputs satisfying the containments; reason: the program needs x₀, r, R (AnalyticCenter, Proposition 5, takes them); correctness of Algorithm 5 for every center x̂ without the balls is Lemma 29
--   - encoding: m, n implicit, natural logs → m ≥ 1, n ≥ 1; Real.log; reason: §2.1: all logs are natural
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Theorem 2, p.3 (PDF p.5), restated with Algorithm 8 and its proof on pp.50–51 (PDF pp.52–53)

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PolySampIso_Machine
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Theorem 2** (PTERRYS: sampling the uniform distribution on a polytope).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Theorem 2, p.3 (PDF p.5), restated with its proof
on pp.50–51 (PDF pp.52–53):

"Theorem 2. Let δ ∈ (0, 1/2). PTERRYS (Algorithm 8), or Algorithm 5, using Algorithm 7 as O with
τ = ⌈C log(m/δ)⌉ for a universal constant C > 0, outputs x satisfying TV(Law(x), π) ≤ δ. Moreover,
if the algorithm is given x0 ∈ X with B2(x0, r) ⊂ X ⊂ B2(x0, R) for known 0 < r < R, it runs in
time O(m²n^{ω−1} log³(m/δ) + m^{3/2} n^{ω−1} log(mR log(1/δ)/r))."

**Formalization Note.**
* The machine is `PolySampIso.Machine`, the real RAM of §2.1 with unit-cost `+ − × ÷`, `√`,
  `exp`, `log`, rational literals, and one-dimensional `N(0,1)` and `Exp(1)` draws. One
  `Admissible` program `P` serves every input. It receives `m, n` in pointers `0, 1`, the scalars
  `δ, r, R` in cells `0, 1, 2`, then `x₀`, `A` (row major) and `b` (`inputState`), and writes its
  output `x ∈ ℝⁿ` to cells `−1, …, −n`.
* "There is a program" replaces the named PTERRYS: Algorithm 8 calls AnalyticCenter, which the
  paper gives only as an existence statement (Proposition 5).
* `ω` is `OAI.MatrixMultiplication.Arithmetic.omega ℝ`, an infimum that need not be attained, so
  `O(n^{ω−1})` is read as `n^{ω−1+ε}` for every `ε > 0`, with `ε` chosen before the program. `O(·)`
  is a constant `C > 0` chosen with `P`, before all inputs. All logs are natural.
* The time bound holds on every pair of random streams (worst case); the output map
  `streams ↦ x` is measurable; `TV(Law(x), π) ≤ δ` is `|P(x ∈ B) − π(B)| ≤ δ` for every
  measurable `B`, with `π = uniform A b` the normalized Lebesgue measure on `X = {Ax < b}`.
* `B₂(x₀, r) ⊂ X` is the open ball, `X ⊂ B₂(x₀, R)` the closed ball (the weakest choices). They
  imply that `X` is nonempty, full-dimensional and bounded, that `A` has full column rank and that
  `m ≥ n + 1`. Both clauses are stated under these hypotheses, since the program needs `x₀`. -/
theorem theorem_2 :
    ∀ ε : ℝ, 0 < ε → ∃ P : Program, Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n →
      ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
        (r R δ : ℝ), 0 < r → r < R → 0 < δ → δ < 1 / 2 →
        Metric.ball x₀ r ⊆ polytope A b → polytope A b ⊆ Metric.closedBall x₀ R →
        let ω := OAI.MatrixMultiplication.Arithmetic.omega ℝ
        let T := C * ((m : ℝ) ^ 2 * (n : ℝ) ^ (ω - 1 + ε) * Real.log (m / δ) ^ 3 +
          (m : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (ω - 1 + ε) *
            Real.log (m * R * Real.log (1 / δ) / r))
        let s₀ := inputState ![δ, r, R] x₀ A b []
        (∀ ωs : Streams, ∃ k, (run P s₀ ωs k).halted = true ∧ ((run P s₀ ωs k).work : ℝ) ≤ T) ∧
        Measurable (finalOutput n P s₀) ∧
        ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
          |tape.real (finalOutput n P s₀ ⁻¹' B) - (uniform A b).real B| ≤ δ := by sorry

end PolySampIso
