-- Prove2me | Theorems.Thm_UnknownBudgetAdwords_alpha_bound
-- name    : UnknownBudgetAdwords.alpha_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:30.348447+00:00
-- url     : https://prove2.me/theorems/57fe3971-100d-4045-97e0-582780b58d0c
-- title:
--   The numeric step: $\alpha>0.522$ at $\beta=1.15$ and $\alpha>0.508$ at $\beta=1$
-- statement:
--   Let
--
--   $$
--   \alpha=\min_{v\in[0,1]}\Big[1-g(v)+\int_0^v\min\Big\{g(y),\frac{g(v)-g(y)}{1-g(y)}\Big\}\,dy\Big].
--   $$
--
--   For $g(x)=e^{1.15(x-1)}$ we have $\alpha>0.522$, and for $g(x)=e^{x-1}$ we have $\alpha>0.508$.
--
--   These two constants are the competitive ratios of Theorem 2. The paper obtains them numerically; the statement here is the bound itself, for all $v\in[0,1]$.
--
--   Differences from the source:
--   - encoding: α is a minimum over [0, 1] with α > c → some number above c bounds the bracket below on [0, 1]; reason: this is what α > c says, and it does not need the minimum to be shown attained
-- source:
--   Udwani, Adwords with Unknown Budgets and Beyond, arXiv:2110.00504v5, proof of Theorem 2, p.21

import Definitions.Def_UnknownBudgetAdwords_Augment
open MehtaOnlineAdAllocation.MSVV
open StochasticRewardMatching.Decomposable (Seeds)
noncomputable section

namespace UnknownBudgetAdwords

/-- The numeric step of the proof of Theorem 2 (Udwani, arXiv:2110.00504v5, proof of Theorem 2,
p.21): `α = min_{v ∈ [0, 1]} [1 − g(v) + ∫_0^v min {g(y), (g(v) − g(y)) / (1 − g(y))} dy]` satisfies
`α > 0.522` for `g(x) = e^{1.15 (x − 1)}` and `α > 0.508` for `g(x) = e^{x − 1}`.

**Formalization Note** `α > c` is stated as: some number above `c` bounds the bracket below on
`[0, 1]`. The location of the minimum is commentary and is not stated. -/
theorem alpha_bound : (∃ c : ℝ, 0.522 < c ∧ ∀ v ∈ Set.Icc (0 : ℝ) 1, c ≤ alphaAt 1.15 v) ∧ (∃ c : ℝ, 0.508 < c ∧ ∀ v ∈ Set.Icc (0 : ℝ) 1, c ≤ alphaAt 1 v) := by sorry

end UnknownBudgetAdwords
