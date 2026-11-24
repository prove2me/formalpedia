-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UJClassFin_mulVec_single__bf9be0aca3c7
-- name    : P2M_PI_UnitaryGroupMassFormula_UJClassFin_mulVec_single__bf9be0aca3c7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:07:38.865061+00:00
-- url     : https://prove2.me/theorems/d6293e2b-91d9-4667-a204-ef3da4a3ca89
-- title:
--   P2 M PI Unitary Group Mass Formula UJClass Fin mul Vec single  bf9be0aca3c7: P2 M PI Unitary Group Mass Formula UJClass Fin mul Vec single  bf9be0aca3c7
-- statement:
--   The P2 M PI Unitary Group Mass Formula UJClass Fin mul Vec single  bf9be0aca3c7 construction uses the P2 M PI Unitary Group Mass Formula UJClass Fin mul Vec single  bf9be0aca3c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/RationalPointsDense.lean#L29-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem P2M_PI_UnitaryGroupMassFormula_UJClassFin_mulVec_single__bf9be0aca3c7 (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (j : Fin M) (x : Af F ⊗[F] E) :
    g.mulVec (Pi.single j x) = fun l => g l j * x := by sorry

alias «PI».«UnitaryGroupMassFormula».«UJClassFin».«mulVec_single'» := P2M_PI_UnitaryGroupMassFormula_UJClassFin_mulVec_single__bf9be0aca3c7
