-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_of_frame
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_of_frame
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:57.734168+00:00
-- url     : https://prove2.me/theorems/23665307-21c4-4c24-aef1-45dd36fc34bd
-- title:
--   BReps: grade of frame
-- statement:
--   The BReps construction uses the grade of frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L129-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/GradeColMatMulVec.lean#L129-L154

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_of_frame {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}
    {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by sorry
