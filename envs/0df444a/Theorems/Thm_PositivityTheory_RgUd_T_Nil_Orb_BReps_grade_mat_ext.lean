-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_mat_ext
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_mat_ext
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:00.538863+00:00
-- url     : https://prove2.me/theorems/9c68da2b-3034-4228-a6f1-6dd539c8ae24
-- title:
--   BReps: grade mat ext
-- statement:
--   The BReps construction uses the grade mat ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L25-L28

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_mat_ext {ι : Type} (b : Module.Basis ι k (Fin n → k)) (X Y : Matrix (Fin n) (Fin n) k)
    (h : ∀ i, X *ᵥ b i = Y *ᵥ b i) : X = Y := by sorry
