-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_finMat_emb
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.finMat_emb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:58.513086+00:00
-- url     : https://prove2.me/theorems/b495418a-cbad-41fd-a700-e819366bc143
-- title:
--   UJClass Fin: fin Mat emb
-- statement:
--   The UJClass Fin construction uses the fin Mat emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/Development.lean#L45-L51

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.finMat_emb (g : UJ (σ : E →+* E) J) :
    finMat σ J (emb σ J g) = ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (Af F)) := by sorry
