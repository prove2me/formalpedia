-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_stabilizer_fixes_frame_vector
-- name    : PI.VolSemiDirect.W.stabilizer_fixes_frame_vector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:27.251068+00:00
-- url     : https://prove2.me/theorems/c5fdfa52-fb0b-405c-80ac-6c3ec756c204
-- title:
--   W: stabilizer fixes frame vector
-- statement:
--   The W construction uses the stabilizer fixes frame vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/StabilizerFixesFrameVector.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/StabilizerFixesFrameVector.lean#L16-L20

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

theorem PI.VolSemiDirect.W.stabilizer_fixes_frame_vector {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P) (a : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by sorry
