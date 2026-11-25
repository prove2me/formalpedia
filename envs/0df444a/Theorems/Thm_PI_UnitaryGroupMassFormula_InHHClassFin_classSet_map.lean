-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_classSet_map
-- name    : PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:10.44502+00:00
-- url     : https://prove2.me/theorems/ef159022-4b94-4fad-a866-105eedeb7fd2
-- title:
--   In HHClass Fin: class Set map
-- statement:
--   The In HHClass Fin construction uses the class Set map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/ClassSetFinIdx.lean#L46-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianClassFiniteness/ClassSetFinIdx.lean#L46-L78

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

theorem PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ K : Subgroup G) :
    Finite (Formalism.UG.ClassSet (Γ.map Φ.toMonoidHom) (K.map Φ.toMonoidHom)) →
      Finite (Formalism.UG.ClassSet Γ K) := by sorry
