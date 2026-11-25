-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_exists_equiv_ls
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_equiv_ls
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:08.270401+00:00
-- url     : https://prove2.me/theorems/582ca58d-2765-40fe-88c8-f71edc3ba81e
-- title:
--   BReps: exists equiv ls
-- statement:
--   The BReps construction uses the exists equiv ls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ExistsEquivLs.lean#L45-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/ExistsEquivLs.lean#L45-L74

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

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_equiv_ls [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) (m : M) :
    ∃ e : F₁.ι m ≃ F₂.ι m, ∀ a, F₂.l m (e a) = F₁.l m a ∧ F₂.s m (e a) = F₁.s m a := by sorry
