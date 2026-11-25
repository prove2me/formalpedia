-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul__c42d1c934366
-- name    : P2M_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul__c42d1c934366
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:01:11.498652+00:00
-- url     : https://prove2.me/theorems/ab44e7b5-8482-5cfb-8ad9-fae56143166a
-- title:
--   P2 M PI Unitary Group Mass Formula UJClass Fin nsmul tmul  c42d1c934366: P2 M PI Unitary Group Mass Formula UJClass Fin nsmul tmul  c42d1c934366
-- statement:
--   The P2 M PI Unitary Group Mass Formula UJClass Fin nsmul tmul  c42d1c934366 construction uses the P2 M PI Unitary Group Mass Formula UJClass Fin nsmul tmul  c42d1c934366 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L61-L67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem P2M_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul__c42d1c934366 (m n : ℕ) (a : Af F) (e : E) :
    (m * n) • (a ⊗ₜ[F] e) = ((m : Af F) * a) ⊗ₜ[F] ((n : E) * e) := by sorry

alias «PI».«UnitaryGroupMassFormula».«UJClassFin».«nsmul_tmul'» := P2M_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul__c42d1c934366
