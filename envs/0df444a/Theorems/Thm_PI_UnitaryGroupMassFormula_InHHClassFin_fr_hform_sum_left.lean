-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_hform_sum_left
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.fr_hform_sum_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:26.622162+00:00
-- url     : https://prove2.me/theorems/0d6e47a4-76c7-4dfa-b6b1-014876125dbd
-- title:
--   In HHClass Fin: fr hform sum left
-- statement:
--   The In HHClass Fin construction uses the fr hform sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/FrHformSumLeft.lean#L50-L55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

theorem PI.UnitaryGroupMassFormula.InHHClassFin.fr_hform_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin I.n → I.E) (y : Fin I.n → I.E) :
    hform (starRingEnd I.E) I.J (∑ i ∈ s, x i) y = ∑ i ∈ s, hform (starRingEnd I.E) I.J (x i) y := by sorry
