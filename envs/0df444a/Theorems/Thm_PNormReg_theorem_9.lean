-- Prove2me | Theorems.Thm_PNormReg_theorem_9
-- name    : PNormReg.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:01.947456+00:00
-- url     : https://prove2.me/theorems/c3d6f937-745f-409f-8b6c-9fd3a30b0b8d
-- title:
--   Theorem 9, p.20 — an $\epsilon$-additive solution of (11) with probability $1-\delta$ in time $\widetilde O_p(nd^{\omega-1})$
-- statement:
--   Let $f(x)=a^\top x+x^\top Qx+\|Nx-b\|_p^p$ be the objective of problem (11), with $N\in\mathbb R^{n\times d}$ of full column rank, $Q\succeq0$, $C\in\mathbb R^{m\times d}$, $m\le d$, and $Cx=\ell$ feasible. For $p\ge2$, $\epsilon>0$ and $\delta\in(0,1)$, there is an algorithm which, given a feasible $x^{(0)}$ and $\nu_0\ge f(x^{(0)})-f^\star$, returns an $\epsilon$-additive approximate solution with probability at least $1-\delta$ in time $\widetilde O_p(nd^{\omega-1})$, where $\widetilde O_p$ also suppresses logarithmic dependence on $\nu_0$.
--
--   Precisely: for every $\tau>0$ there are one admissible program and constants $C>0$, $K\in\mathbb N$ such that, on every instance with $d\ge1$, every coin tape halts within
--
--   $$C\,p^K\,n^{1+\tau}\,d^{\omega-1}\,\big(\log(2+n+1/\delta)+\log(2+\nu_0/\epsilon)\big)^K$$
--
--   steps, and a measurable set of tapes of probability at least $1-\delta$ gives an output $\hat x$ with $C\hat x=\ell$ and $f(\hat x)\le f(x)+\epsilon$ for every feasible $x$.
--
--   This is the engine of the paper: it powers Theorem 2 and the sparse dual solve behind Theorem 3.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of the randomized exact-arithmetic real RAM PNormReg.Machine: rational literals, + − × ÷, √, unit-cost |r|^s, integer pointers with + −, fair coins; no floor, exp, log, argmin; reason: the paper names no machine and charges one step for each primitive (pp.25, 41); this is the weakest machine its method runs on, so the theorem is the strongest reading
--   - reading: Õ_p(nd^{ω−1}) with Õ, Õ_p as in footnote 2 → ∀τ > 0 ∃ program, C > 0, K ∈ ℕ, then ∀ instance: work ≤ C·p^K·n^(1+τ)·d^(ω−1)·(log(2+n+1/δ) + log(2+ν₀/ϵ))^K; reason: ω is an infimum, so the n^{o(1)} of footnote 2 is "for all δ > 0" of the definition on p.8, one program per slack; p^K is footnote 2's "polynomial in p for our p ≥ 2 results"; no dependence on a condition number
--   - encoding: ω := ω(1,1,1), p.8 → the published OAI.MatrixMultiplication.Arithmetic.omega ℝ, the infimum of exponents of correct straight-line programs over ℝ; reason: the paper's matrices live over ℝ; the definition adds no condition
--   - reading: "For p ∈ [2, ∞) and ϵ, δ ∈ (0, 1), there is an algorithm" → one program for all p, ϵ, δ, which are part of the input; reason: the paper's algorithm takes them as inputs; a program per parameter value would be the weaker reading
--   - reading: "(randomized) algorithms", p.3 → a tape of independent fair coins, one bit per executed coin instruction; reason: the weakest random primitive; real-valued sampling reduces to it by scanning cumulative sums
--   - reading: with probability at least 1 − δ, in time T → every tape halts within T, and a measurable set of tapes of probability at least 1 − δ gives an accurate output; reason: the paper caps every subroutine (pp.21, 33), so worst-case time is what its proofs give; a measurable set avoids outer measure
--   - encoding: f(x̂) ≤ f⋆ + ϵ → Cx̂ = ℓ and f(x̂) ≤ f(x) + ϵ for every feasible x; reason: the same statement, without the optimal value in the success event
--   - encoding: dimensions n, d → 1 ≤ d; reason: at d = 0 the problem is trivial and d^{ω−1} = 0 would forbid halting
--   - encoding: the input of the algorithm → the dense layout PNormReg.theorem9Input; reason: the paper names no input format; the bound pays for reading all the data
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 9, p.20 (PDF p.21); problem (11), p.18

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_InputLayout

open Matrix

namespace PNormReg

/-- **Theorem 9**, p.20 (PDF p.21).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

"For ϵ > 0 and δ ∈ (0, 1), there is an algorithm which, given an initial feasible point x^(0) and bound
ν0 ≥ f(x^(0)) − f⋆, returns an ϵ-additive approximate solution to (11) with probability at least 1 − δ
in time Õp(nd^{ω−1})."

Same form as `PNormReg.theorem_2`, with the bound
`C·p^K·n^{1+τ}·d^{ω−1}·(log(2 + n + 1/δ) + log(2 + ν₀/ϵ))^K` (p.20: Õ_p also suppresses logarithmic
dependence on `ν₀`). Success is `Cx̂ = ℓ` and `f(x̂) ≤ f(x) + ϵ` for every feasible `x`.

**Formalization Note.** `ϵ` has no upper bound, `m` is free with `m ≤ d`, and `C` need not have full row
rank. `d ≥ 1` as in Theorem 2. The input is `theorem9Input`. -/
theorem theorem_9 :
    ∀ τ : ℝ, 0 < τ →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d m : ℕ), 1 ≤ d → ∀ (G : GenRegression n d m), G.IsStanding →
          ∀ (p ε δ ν₀ : ℝ) (x₀ : Fin d → ℝ), 2 ≤ p → 0 < ε → 0 < δ → δ < 1 →
            G.Feasible x₀ → G.obj p x₀ - G.fStar p ≤ ν₀ →
            (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (theorem9Input G p ε δ ν₀ x₀) ω t).halted = true ∧
              ((run P (theorem9Input G p ε δ ν₀ x₀) ω t).work : ℝ) ≤
                C * p ^ K * (n : ℝ) ^ (1 + τ) *
                  (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ - 1) *
                  (Real.log (2 + n + 1 / δ) + Real.log (2 + ν₀ / ε)) ^ K) ∧
            ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - δ ≤ (coinTape E).toReal ∧
              ∀ ω ∈ E, ∀ t : ℕ, (run P (theorem9Input G p ε δ ν₀ x₀) ω t).halted = true →
                G.Feasible (outputVec d (run P (theorem9Input G p ε δ ν₀ x₀) ω t)) ∧
                ∀ x : Fin d → ℝ, G.Feasible x →
                  G.obj p (outputVec d (run P (theorem9Input G p ε δ ν₀ x₀) ω t)) ≤
                    G.obj p x + ε := by sorry

end PNormReg
