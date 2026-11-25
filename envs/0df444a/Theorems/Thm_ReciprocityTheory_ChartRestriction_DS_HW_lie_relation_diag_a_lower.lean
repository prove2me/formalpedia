-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lie_relation_diag_a_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_diag_a_lower
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:41:18.124579+00:00
-- url     : https://prove2.me/theorems/63b4f379-6f59-4c32-af29-79e0f31e70ae
-- title:
--   HW: lie relation diag a lower
-- statement:
--   The HW construction uses the lie relation diag a lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L29-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_diag_a_lower (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b) (y : M) :
    F a a (F b a y) = F b a (F a a y) - F b a y := by sorry
