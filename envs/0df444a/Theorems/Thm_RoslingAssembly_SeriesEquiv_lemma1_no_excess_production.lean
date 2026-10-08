-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_lemma1_no_excess_production
-- name    : RoslingAssembly.SeriesEquiv.lemma1_no_excess_production
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:45.227991+00:00
-- url     : https://prove2.me/theorems/29843c31-4b5c-4d8e-86e8-cfbebe06b6e2
-- title:
--   Lemma 1 — no excess production
-- statement:
--   Under Rosling’s Assumption, let $\pi$ be an optimal policy and put $m_{it}=\min_{k>i}X^{M_k-M_i}_{kt}$. For every item and period, almost surely,
--
--   $$Y_{it}=X_{it}\quad\text{if }X_{it}\ge m_{it},\qquad X_{it}\le Y_{it}\le m_{it}\quad\text{if }X_{it}\le m_{it}.$$
--
--   The bound rules out producing an item beyond what can be made available as end product within its total lead time.
--
--   **Formalization Note** The minimum is $+\infty$ for the last item. The inequalities hold almost surely because policies may differ on null histories; $0<\alpha<1$ and consistent initial histories are explicit.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 568, Lemma 1, eq. (6); proof pp. 576–577

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv

/-- Rosling, Lemma 1 and (6), p. 568. -/
theorem lemma1_no_excess_production (S : Model) (x0 : InitialPositions)
    (π : Policy) [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hDemand : S.ValidDemand)
    (hα : 0 < S.α ∧ S.α < 1) (hAssumption : S.Assumption)
    (hInitial : S.WellFormedInitial x0) (hOptimal : S.Optimal x0 π) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν),
      ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
        S.NoExcessAt x0 π ω i t := by sorry

end RoslingAssembly.SeriesEquiv
