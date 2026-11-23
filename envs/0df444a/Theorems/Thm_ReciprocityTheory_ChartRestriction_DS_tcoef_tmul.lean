-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_tmul
-- name    : ReciprocityTheory.ChartRestriction.DS.tcoef_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:25.150368+00:00
-- url     : https://prove2.me/theorems/415c513b-3fe5-4f84-8628-475d269518c4
-- title:
--   DS: tcoef tmul
-- statement:
--   The DS construction uses the tcoef tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L15-L16

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

theorem ReciprocityTheory.ChartRestriction.DS.tcoef_tmul (φ : Module.Dual ℂ (Fock n)) (m : M) (f : Fock n) : tcoef φ (m ⊗ₜ f) = φ f • m := by sorry
