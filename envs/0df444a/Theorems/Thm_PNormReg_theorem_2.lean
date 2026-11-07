-- Prove2me | Theorems.Thm_PNormReg_theorem_2
-- name    : PNormReg.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:08.96114+00:00
-- url     : https://prove2.me/theorems/cac04aef-6f74-41e4-b89d-2c9ebdd72e5a
-- title:
--   Theorem 2, p.2 — a $(1+\epsilon)$-approximate $\ell_p$-regression solution for every $p\ge2$, with probability $1-\delta$, in time $\widetilde O_p(nd^{\omega-1})$
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$, $p\in[2,\infty)$ and $\epsilon,\delta\in(0,1)$. There is an algorithm which, with probability at least $1-\delta$, returns $\hat x$ with
--
--   $$\|A\hat x-b\|_p\le(1+\epsilon)\min_x\|Ax-b\|_p,$$
--
--   in time $\widetilde O_p(nd^{\omega-1})$, where $\omega$ is the square matrix multiplication exponent.
--
--   Precisely: for every $\tau>0$ there are one admissible program of the randomized real RAM and constants $C>0$, $K\in\mathbb N$ such that, for all $n$, $d\ge1$, full column rank $A$, $b$, $p\ge2$ and $\epsilon,\delta\in(0,1)$, every coin tape halts within
--
--   $$C\,p^K\,n^{1+\tau}\,d^{\omega-1}\,\big(\log(2+n+1/\epsilon+1/\delta)\big)^K$$
--
--   steps, and a measurable set of tapes of probability at least $1-\delta$ gives an accurate output.
--
--   The bound depends on $p$ only polynomially and has no dependence on a condition number of $A$. With $n=\widetilde O(d)$ it is the first $\widetilde O(d^\omega)$-time high-accuracy algorithm for each fixed $p>2$ under any value of $\omega$.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of the randomized exact-arithmetic real RAM PNormReg.Machine: rational literals, + − × ÷, √, unit-cost |r|^s, integer pointers with + −, fair coins; no floor, exp, log, argmin; reason: the paper names no machine and charges one step for each primitive (pp.25, 41); this is the weakest machine its method runs on, so the theorem is the strongest reading
--   - reading: Õ_p(nd^{ω−1}) with Õ, Õ_p as in footnote 2 → ∀τ > 0 ∃ program, C > 0, K ∈ ℕ, then ∀ instance: work ≤ C·p^K·n^(1+τ)·d^(ω−1)·(log(2+n+1/ϵ+1/δ))^K; reason: ω is an infimum, so the n^{o(1)} of footnote 2 is "for all δ > 0" of the definition on p.8, one program per slack; p^K is footnote 2's "polynomial in p for our p ≥ 2 results"; no dependence on a condition number
--   - encoding: ω := ω(1,1,1), p.8 → the published OAI.MatrixMultiplication.Arithmetic.omega ℝ, the infimum of exponents of correct straight-line programs over ℝ; reason: the paper's matrices live over ℝ; the definition adds no condition
--   - reading: "For p ∈ [2, ∞) and ϵ, δ ∈ (0, 1), there is an algorithm" → one program for all p, ϵ, δ, which are part of the input; reason: the paper's algorithm takes them as inputs; a program per parameter value would be the weaker reading
--   - reading: "(randomized) algorithms", p.3 → a tape of independent fair coins, one bit per executed coin instruction; reason: the weakest random primitive; real-valued sampling reduces to it by scanning cumulative sums
--   - reading: with probability at least 1 − δ, in time T → every tape halts within T, and a measurable set of tapes of probability at least 1 − δ gives an accurate output; reason: the paper caps every subroutine (pp.21, 33), so worst-case time is what its proofs give; a measurable set avoids outer measure
--   - encoding: f_p(x̂) ≤ (1 + ϵ)f⋆_p → ∀ x, ∥Ax̂ − b∥_p ≤ (1 + ϵ)∥Ax − b∥_p; reason: equivalent because the minimum exists; f⋆_p = 0 is included and then forces Ax̂ = b
--   - encoding: "full column rank (implying n ≥ d)", footnote 1 → Function.Injective A.mulVec and 1 ≤ d; reason: at d = 0 the problem is trivial and d^{ω−1} = 0 would forbid halting; n ≥ d follows from injectivity
--   - encoding: the input of the algorithm → the dense layout PNormReg.goalInput; the output in cells −1 − j; reason: the paper names no input format; the bound pays for reading all of A
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 2, p.2 (PDF p.3); problem (1) and footnotes 1–2, p.1; ω, p.8

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_InputLayout

open Matrix

namespace PNormReg

/-- **Theorem 2** (High-accuracy `ℓ_p`-regression for `p ∈ [2, ∞)`).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 2, p.2 (PDF p.3); problem (1) and footnotes 1–2, p.1.

"For p ∈ [2, ∞) and ϵ, δ ∈ (0, 1), there is an algorithm which returns a (1 + ϵ)-approximate solution to
(1), with probability at least 1 − δ, in time Õ_p(nd^{ω−1})."

For every `τ > 0` there are one admissible program `P` and constants `C > 0`, `K ∈ ℕ` such that for all
`n`, `d ≥ 1`, full column rank `A`, `b`, `p ≥ 2` and `ϵ, δ ∈ (0, 1)`, with
`T = C·p^K·n^{1+τ}·d^{ω−1}·(log(2 + n + 1/ϵ + 1/δ))^K`:
every coin tape halts with `work ≤ T`, and a measurable set of tapes of probability at least `1 − δ`
gives a halted output `x̂` with `∥Ax̂ − b∥_p ≤ (1 + ϵ)∥Ax − b∥_p` for all `x`.

**Formalization Note.**
* ω is the published `OAI.MatrixMultiplication.Arithmetic.omega ℝ`, an infimum, so `∀ τ` comes first:
  this is "for all δ > 0" in the paper's definition of ω (p.8) and the `n^{o(1)}` of footnote 2.
* `p^K` is footnote 2's "polynomial in p for our p ≥ 2 results"; one program serves every `p ≥ 2`, because
  `p` is an input.
* The time bound holds on every tape. The output's accuracy holds on the measurable set.
* `f⋆_p` is written as `∀ x`, equivalent since the minimum exists; `f⋆_p = 0` is included.
* `d ≥ 1`: at `d = 0`, `d^{ω−1} = 0` would forbid halting. `n ≥ d` follows from injectivity. -/
theorem theorem_2 :
    ∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ p ε δ : ℝ, 2 ≤ p → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (goalInput A b p ε δ) ω t).halted = true ∧
              ((run P (goalInput A b p ε δ) ω t).work : ℝ) ≤
                C * p ^ K * (n : ℝ) ^ (1 + τ) *
                  (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (goalInput A b p ε δ) ω t).halted = true →
                ∀ x : Fin d → ℝ,
                  lpNorm p (A *ᵥ outputVec d (run P (goalInput A b p ε δ) ω t) - b) ≤
                    (1 + ε) * lpNorm p (A *ᵥ x - b) := by sorry

end PNormReg
