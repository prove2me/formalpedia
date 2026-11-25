-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_smul
-- name    : ReciprocityTheory.ChartRestriction.DS.tcoef_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:26.927498+00:00
-- url     : https://prove2.me/theorems/0d1cbaf2-c75c-5e35-994b-71279cd1d05b
-- title:
--   DS: tcoef smul
-- statement:
--   The DS construction uses the tcoef smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean#L33-L38

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

theorem ReciprocityTheory.ChartRestriction.DS.tcoef_smul (c : ℂ) (φ : Module.Dual ℂ (Fock n)) (y : TensorProduct ℂ M (Fock n)) :
    tcoef (c • φ) y = c • tcoef φ y := by sorry
