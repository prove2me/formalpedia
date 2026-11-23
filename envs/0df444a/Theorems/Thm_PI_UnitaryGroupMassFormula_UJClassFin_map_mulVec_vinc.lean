-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_map_mulVec_vinc
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:00.837339+00:00
-- url     : https://prove2.me/theorems/fb48edf3-61a2-43f8-bc76-4b212a388026
-- title:
--   UJClass Fin: map mul Vec vinc
-- statement:
--   The UJClass Fin construction uses the map mul Vec vinc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L53-L58

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
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
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc (A : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (A.map (inclR (Af F))).mulVec (vinc (F := F) x) = vinc (F := F) (A.mulVec x) := by sorry
