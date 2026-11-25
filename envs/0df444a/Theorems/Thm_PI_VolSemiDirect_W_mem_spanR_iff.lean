-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_mem_spanR_iff
-- name    : PI.VolSemiDirect.W.mem_spanR_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:37:47.810687+00:00
-- url     : https://prove2.me/theorems/9e826233-4918-5224-b768-a796633541d3
-- title:
--   W: mem span R iff
-- statement:
--   The W construction uses the mem span R iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L66-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L66-L97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_Closed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R}

theorem PI.VolSemiDirect.W.mem_spanR_iff {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m))
    (P : Matrix (Fin n) (Fin n) E) (hP1 : ∀ x, P *ᵥ x ∈ Submodule.span E (Y '' s))
    (hP2 : ∀ x ∈ Submodule.span E (Y '' s), P *ᵥ x = x) (v : Fin n → R ⊗[F] E) :
    v ∈ spanR (F := F) R Y s ↔ (P.map (inclR (F := F) R)) *ᵥ v = v := by sorry
