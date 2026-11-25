-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_bVR_apply
-- name    : PI.VolSemiDirect.W.Cj.bVR_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:35.641653+00:00
-- url     : https://prove2.me/theorems/8b4b6d59-4a0e-5925-b19a-f1325fa4e664
-- title:
--   Cj: b VR apply
-- statement:
--   The Cj construction uses the b VR apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/BVRApply.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/BVRApply.lean#L24-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_BVRApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct Matrix
variable (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (M : ℕ)
  (A : Type) [CommRing A] [Algebra F A]

theorem PI.VolSemiDirect.W.Cj.bVR_apply (i : Fin (Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E)))) :
    bVR F E M A i = ratV (F := F) A (bV F E M i) := by sorry
