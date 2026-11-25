-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_eig
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_eig
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:54.794045+00:00
-- url     : https://prove2.me/theorems/286b3ef2-80cc-557f-9ce9-c59700878a4e
-- title:
--   BReps: grade eig
-- statement:
--   The BReps construction uses the grade eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L30-L41

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_eig {ι : Type} (b : Module.Basis ι k (Fin n → k)) (g : Matrix (Fin n) (Fin n) k) (d : ι → k)
    (hg : ∀ i, g *ᵥ b i = d i • b i) (S : Set ι) (c : k) (hS : ∀ i ∈ S, d i = c) (y : Fin n → k)
    (hy : y ∈ span k (b '' S)) : g *ᵥ y = c • y := by sorry
