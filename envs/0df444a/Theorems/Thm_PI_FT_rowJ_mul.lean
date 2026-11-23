-- Prove2me | Theorems.Thm_PI_FT_rowJ_mul
-- name    : PI.FT.rowJ_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:00.735596+00:00
-- url     : https://prove2.me/theorems/40a3ccd8-a7dd-428f-85cb-2f5865ec5926
-- title:
--   FT: row J mul
-- statement:
--   The FT construction uses the row J mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L28-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}

theorem PI.FT.rowJ_mul {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin 1 → Fin n → E)
    (C : Matrix (Fin n) (Fin m) E) (k : Fin m) :
    ((Matrix.of v).map σ * J * C) 0 k = hE σ J (v 0) (fun i => C i k) := by sorry
