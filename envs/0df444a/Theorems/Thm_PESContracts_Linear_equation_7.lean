-- Prove2me | Theorems.Thm_PESContracts_Linear_equation_7
-- name    : PESContracts.Linear.equation_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:26.884738+00:00
-- url     : https://prove2.me/theorems/086320de-55e8-4d37-b018-2558c4ff9040
-- title:
--   Equation (7), p. 10 — doubled payoff at price k/2
-- statement:
--   Let $a_0,h,k>0$, and let $\mu$ be any probability distribution supported on $[\underline\theta,\bar\theta]\subseteq[0,1]$. At the linear-contract price $p=k/2$, twice the expected payoff is the expectation of the following typewise quantity:
--
--   $$
--   2\operatorname{Obj}^L(k/2)
--   =\mathbb E_\mu\!\left[
--     \begin{cases}
--     k\theta a_0+k^2/(2h),&\theta\leq\tilde\theta(k/2),\\
--     k a_0,&\theta>\tilde\theta(k/2).
--     \end{cases}\right]
--   $$
--
--   This is Equation (7)'s doubled linear payoff and is the comparison quantity in the proof of Theorem 1.
--
--   **Formalization Note** The expectation and threshold split include discrete type laws. They also handle a threshold outside the support without interpreting a reversed integration interval.
-- source:
--   Li, Ashlagi & Lo, Simple and Approximately Optimal Contracts for Payment for Ecosystem Services, SSRN preprint 3754041 (version of 2021-05-19), p. 10, Equation (7), and p. 25, proof of Theorem 1; https://ssrn.com/abstract=3754041

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
open MeasureTheory

namespace PESContracts.Linear

/-- Equation (7), p. 10, with its threshold split interpreted pointwise. -/
theorem equation_7 (M : Params) (hM : M.Standing) (k : ℝ) (hk : 0 < k)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ M.typesᶜ = 0) :
    2 * ObjL M k μ (k / 2) =
      ∫ θ, (if θ ≤ θtilde M (k / 2)
        then k * θ * M.a0 + k ^ 2 / (2 * M.h)
        else k * M.a0) ∂μ := by sorry

end PESContracts.Linear
