-- Prove2me | Theorems.Thm_QPK_isGrp_pi
-- name    : QPK.isGrp_pi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:23.818465+00:00
-- url     : https://prove2.me/theorems/1fc561ff-b56a-4e95-aaee-85accc4c8efe
-- title:
--   QPK: is Grp pi
-- statement:
--   The QPK construction uses the is Grp pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/WeilQuotientGlobalAssumptions.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/WeilQuotientGlobalAssumptions.lean#L15-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_WeilQuotientGlobalAssumptions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)]

theorem QPK.isGrp_pi (K : ∀ v, Set (G v)) (hK : ∀ v, IsGrp (K v)) : IsGrp (Set.pi univ K) := by sorry
