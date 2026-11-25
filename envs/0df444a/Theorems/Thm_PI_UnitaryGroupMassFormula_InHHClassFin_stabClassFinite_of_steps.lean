-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_stabClassFinite_of_steps
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:41:53.0038+00:00
-- url     : https://prove2.me/theorems/9db65799-dfb6-44a1-a472-f40162561d94
-- title:
--   In HHClass Fin: stab Class Finite of steps
-- statement:
--   The In HHClass Fin construction uses the stab Class Finite of steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/Development.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/Development.lean#L150-L154

import Definitions.Def_Formalism_PeriodIntegrals_InHHClassFin
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_Final_SigConj

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps (hMono : ClassSetMono) (hIdx : ClassSetFinIdx)
    (hMap : ClassSetMap) (hTop : KgNhd) (hSig : SigConj) (hE : FrameExists) (hIso : FrameIso)
    (hG : FrameGram) (hRat : FrameRat) (hLev : LevelStep) : StabClassFinite := by sorry
