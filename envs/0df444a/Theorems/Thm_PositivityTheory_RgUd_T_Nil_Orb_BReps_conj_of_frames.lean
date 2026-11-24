-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_conj_of_frames
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.conj_of_frames
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:08.258575+00:00
-- url     : https://prove2.me/theorems/e1486938-b822-419d-ad17-46a78f7c71dd
-- title:
--   BReps: conj of frames
-- statement:
--   The BReps construction uses the conj of frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ExistsEquivLs.lean#L76-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ExistsEquivLs.lean#L76-L141

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ExistsEquivLs
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
variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.conj_of_frames [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) :
    ∃ g : GL (Fin n) k, (∀ a ∈ Z, a * g.val = g.val * a) ∧ g.val * N₁ = N₂ * g.val ∧ g.val *ᵥ v₁ = v₂ := by sorry
