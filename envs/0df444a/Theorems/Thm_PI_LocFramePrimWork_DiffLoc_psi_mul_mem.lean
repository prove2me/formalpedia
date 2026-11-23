-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_mul_mem
-- name    : PI.LocFramePrimWork.DiffLoc_psi_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:29.072086+00:00
-- url     : https://prove2.me/theorems/7032a71a-6050-4f87-b53c-33e07a85bfb0
-- title:
--   Loc Frame Prim Work: Diff Loc psi mul mem
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc psi mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L28-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
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
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocFramePrimWork.DiffLoc_psi_mul_mem (S : Set E) (hS : ∀ (o : 𝓞 E) (s : E), s ∈ S → (o : E) * s ∈ S)
    {y : Fv F v ⊗[F] E} (hy : y ∈ DiffLoc_psi v S) (o : 𝓞 E) :
    inclR (F := F) (Fv F v) (o : E) * y ∈ DiffLoc_psi v S := by sorry
