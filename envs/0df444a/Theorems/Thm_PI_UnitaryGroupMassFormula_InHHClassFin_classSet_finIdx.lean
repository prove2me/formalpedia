-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_classSet_finIdx
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.classSet_finIdx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:38.923532+00:00
-- url     : https://prove2.me/theorems/566afa09-a1ee-4acf-a74c-3afab1bef093
-- title:
--   In HHClass Fin: class Set fin Idx
-- statement:
--   The In HHClass Fin construction uses the class Set fin Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/ClassSetFinIdx.lean#L23-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/ClassSetFinIdx.lean#L23-L44

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.classSet_finIdx {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K' ≤ K)
    (hi : K'.relIndex K ≠ 0) :
    Finite (Formalism.UG.ClassSet Γ K) → Finite (Formalism.UG.ClassSet Γ K') := by sorry
