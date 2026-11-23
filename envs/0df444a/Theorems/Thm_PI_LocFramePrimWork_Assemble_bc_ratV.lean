-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_bc_ratV
-- name    : PI.LocFramePrimWork.Assemble_bc_ratV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:40.145662+00:00
-- url     : https://prove2.me/theorems/1f5d6299-90bd-46db-8a09-82af82b5c640
-- title:
--   Loc Frame Prim Work: Assemble bc rat V
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble bc rat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L19-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem PI.LocFramePrimWork.Assemble_bc_ratV (ψ : (Fin n → E) →ₗ[E] E) (y : Fin n → E) :
    Assemble_bc v ψ (ratV (F := F) (Fv F v) y) = inclR (F := F) (Fv F v) (ψ y) := by sorry
