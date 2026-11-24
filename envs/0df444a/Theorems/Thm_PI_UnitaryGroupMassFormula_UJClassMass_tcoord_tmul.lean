-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_tcoord_tmul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.tcoord_tmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:39:36.453826+00:00
-- url     : https://prove2.me/theorems/124cd4bf-9dc8-4a40-8650-194707fe9b37
-- title:
--   UJClass Mass: tcoord tmul
-- statement:
--   The UJClass Mass construction uses the tcoord tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PHermT.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PHermT.lean#L20-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass

theorem PI.UnitaryGroupMassFormula.UJClassMass.tcoord_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] (x : E) (y : R) :
    tcoord B k R (x ⊗ₜ[F] y) = B.coord k x • y := by sorry
