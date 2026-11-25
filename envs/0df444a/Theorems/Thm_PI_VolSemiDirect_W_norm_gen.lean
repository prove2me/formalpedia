-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_norm_gen
-- name    : PI.VolSemiDirect.W.norm_gen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:45.565614+00:00
-- url     : https://prove2.me/theorems/e8ab3d00-3a35-430d-9879-9842b383f432
-- title:
--   W: norm gen
-- statement:
--   The W construction uses the norm gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/StabilizerFixesFrameVector.lean#L32-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/StabilizerFixesFrameVector.lean#L32-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.VolSemiDirect.W.norm_gen {r : ℕ} (P : Frame E M r) (h : HA R σ J) (hh : h ∈ Hsub R σ J P)
    (n : HA R σ J) (hn : n ∈ FrameUnipotentSubgroup R σ J P) : h * n * h⁻¹ ∈ FrameUnipotentSubgroup R σ J P := by sorry
