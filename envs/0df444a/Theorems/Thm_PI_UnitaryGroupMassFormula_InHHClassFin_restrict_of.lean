-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_restrict_of
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.restrict_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:41:39.756349+00:00
-- url     : https://prove2.me/theorems/0e69a15f-f075-4824-ab03-45d63f73a65e
-- title:
--   In HHClass Fin: restrict of
-- statement:
--   The In HHClass Fin construction uses the restrict of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/Development.lean#L135-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/Development.lean#L135-L148

import Definitions.Def_Formalism_PeriodIntegrals_InHHClassFin
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain Formalism.UG PI.InHHClassFin
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin

theorem PI.UnitaryGroupMassFormula.InHHClassFin.restrict_of (hE : FrameExists) (hIso : FrameIso) (hG : FrameGram) (hRat : FrameRat)
    (hLev : LevelStep) (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) (hS : DefiniteCompl I S) :
    Restrict I S := by sorry
