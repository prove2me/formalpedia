-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_thm2_cost_rewrite
-- name    : RoslingAssembly.SeriesEquiv.thm2_cost_rewrite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:48.138802+00:00
-- url     : https://prove2.me/theorems/9377af51-374b-4306-9c7e-653a68bf3e14
-- title:
--   Proof of Theorem 2 — cost rewrite
-- statement:
--   For every policy, the original and equivalent series systems assign the same objective (2), because the series holding coefficient is $h_i\alpha^{l_i-L_i}$ and its lead time is $L_i$.
--
--   $$C_{\mathrm{assembly}}(\pi)=C_{\mathrm{series}}(\pi).$$
--
--   This identifies the cost term after the series transformation, independently of the feasibility comparison.
--
--   **Formalization Note** Both objectives omit the same policy-independent constant (4); the equivalent demand convolution agrees because $L_1=l_1$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 569, proof of Theorem 2, first displayed formula

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv

/-- The cost identity at the start of the proof of Rosling's Theorem 2,
p. 569. Both sides are objective (2), without its fixed constant. -/
theorem thm2_cost_rewrite (S : Model) (π : Policy)
    [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hα : 0 < S.α ∧ S.α < 1) :
    S.cost π = (S.series).cost π := by sorry

end RoslingAssembly.SeriesEquiv
