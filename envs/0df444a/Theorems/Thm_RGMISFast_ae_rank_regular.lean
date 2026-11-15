-- Prove2me | Theorems.Thm_RGMISFast_ae_rank_regular
-- name    : RGMISFast.ae_rank_regular
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T01:12:49.991231+00:00
-- url     : https://prove2.me/theorems/65adc6da-f10c-4d8a-8213-17f5ce5a8ee9
-- title:
--   Independent exponential ranks are almost surely distinct and nonnegative
-- statement:
--   For any finite vertex set V, sample the ranks independently from Exp(1). Then $$\Pr[r\text{ is injective and }\forall v\in V,\ r(v)\ge0]=1.$$ This supplies the rank-regularity clause needed when passing from deterministic query-tree estimates to probability bounds. No graph or vertex ordering is required.
-- source:
--   Randomized Greedy MIS Is Fast at Every Node, §2 p.10 (standing assumptions on ranks), and proof of Theorem 1.1 p.17. Explicit measure-theoretic justification of the almost-sure rank assumptions.

import Definitions.Def_RGMISFast_rankLaw
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem RGMISFast.ae_rank_regular (V : Type) [Fintype V] :
    ∀ᵐ r ∂(RGMISFast.rankLaw V), Function.Injective r ∧ ∀ v, 0 ≤ r v := by sorry
