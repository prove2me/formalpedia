-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lie_relation_raise_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_raise_lower
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:59:00.597289+00:00
-- url     : https://prove2.me/theorems/eb34bcca-1aab-487e-a901-0da5705f6e7e
-- title:
--   HW: lie relation raise lower
-- statement:
--   The HW construction uses the lie relation raise lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean#L19-L27

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

theorem ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_raise_lower (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (he : ε a = ε b) (y : M) :
    F a b (F b a y) = F b a (F a b y) + F a a y - F b b y := by sorry
