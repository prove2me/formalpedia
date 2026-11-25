-- Prove2me | Theorems.Thm_PI_FT_mem_HFinIn_iff
-- name    : PI.FT.mem_HFinIn_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:40.071513+00:00
-- url     : https://prove2.me/theorems/942d8614-a02e-4e01-9992-f2b1dd5b3baf
-- title:
--   FT: mem HFin In iff
-- statement:
--   The FT construction uses the mem HFin In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L152-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L152-L184

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
variable (R : Type) [CommRing R] [Algebra F R]

theorem PI.FT.mem_HFinIn_iff (hinj : Function.Injective (inclR (F := F) (E := E) R))
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    toHR g ∈ HFinIn R σ J ↔
      (∃ a : Matrix (Fin n) (Fin n) E, ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (R ⊗[F] E)) = a.map (inclR (F := F) (E := E) R)) ∧
      (∃ a : Matrix (Fin n) (Fin n) E, (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (R ⊗[F] E)) = a.map (inclR (F := F) (E := E) R)) := by sorry
