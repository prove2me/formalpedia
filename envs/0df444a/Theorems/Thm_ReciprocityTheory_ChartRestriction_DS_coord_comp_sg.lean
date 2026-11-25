-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coord_comp_sg
-- name    : ReciprocityTheory.ChartRestriction.DS.coord_comp_sg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:32.309803+00:00
-- url     : https://prove2.me/theorems/ec1d8cc1-03b5-47a2-918f-28011b41587e
-- title:
--   DS: coord comp sg
-- statement:
--   The DS construction uses the coord comp sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L64-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.coord_comp_sg (ε : Fin n → Bool) (s : Finset (Fin (n * n))) (c : Fin n) :
    (fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock c c = ((fockWt ε s c : ℝ) : ℂ) • (fockBasis n).coord s := by sorry
