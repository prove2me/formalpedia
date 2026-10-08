-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_lemma2_min_production
-- name    : RoslingAssembly.SeriesEquiv.lemma2_min_production
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:11.635978+00:00
-- url     : https://prove2.me/theorems/10b14442-cef9-4594-8729-fa1b264d37d2
-- title:
--   Lemma 2 — minimum production
-- statement:
--   Under Rosling’s Assumption, any optimal policy satisfies, for every item and period almost surely,
--
--   $$Y_{it}\ge\min\left(0,\min_{k>i}X^{M_k-M_i}_{kt}\right).$$
--
--   The lower bound is the production condition used in the realization of long-run balance.
--
--   **Formalization Note** For $i=N$ the inner minimum is $+\infty$, so the bound is $Y_{Nt}\ge0$. Only equation (7) is formalized; the following service-time sentence uses an informal first-come first-served convention.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 568, Lemma 2, eq. (7); proof p. 576

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv

/-- Rosling, Lemma 2 and (7), p. 568. -/
theorem lemma2_min_production (S : Model) (x0 : InitialPositions)
    (π : Policy) [MeasureTheory.IsProbabilityMeasure S.ν]
    (hTree : S.ValidTree) (hDemand : S.ValidDemand)
    (hα : 0 < S.α ∧ S.α < 1) (hAssumption : S.Assumption)
    (hInitial : S.WellFormedInitial x0) (hOptimal : S.Optimal x0 π) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν),
      ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
        S.MinProductionAt x0 π ω i t := by sorry

end RoslingAssembly.SeriesEquiv
