-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_exists_frames
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_frames
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:13.057893+00:00
-- url     : https://prove2.me/theorems/1a5a4361-5796-4fb2-a32b-840ff259dae6
-- title:
--   BReps: exists frames
-- statement:
--   The BReps construction uses the exists frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/Imports.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/Imports.lean#L11-L57

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexGlobal
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_frames (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) :
    ∃ (M : Type) (_ : Fintype M) (L : M → Type) (_ : ∀ m, Fintype (L m)) (_ : ∀ m, Nonempty (L m))
      (R : Z → (m : M) → L m → L m → k) (o : (m : M) → L m → k),
      ∀ N : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * N = N * z) → IsNilpotent N → ∀ v : Fin n → k,
        Nonempty (Frame Z M L R o N v) := by sorry
