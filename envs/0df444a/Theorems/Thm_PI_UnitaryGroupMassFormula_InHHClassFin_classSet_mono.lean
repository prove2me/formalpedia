-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_classSet_mono
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:39:20.562792+00:00
-- url     : https://prove2.me/theorems/94269a79-c367-54ba-b235-238b6c672e1a
-- title:
--   In HHClass Fin: class Set mono
-- statement:
--   The In HHClass Fin construction uses the class Set mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/ClassSetFinIdx.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/ClassSetFinIdx.lean#L8-L21

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_ClassSetFinIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
open DoubleCoset

theorem PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K ≤ K') :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by sorry
