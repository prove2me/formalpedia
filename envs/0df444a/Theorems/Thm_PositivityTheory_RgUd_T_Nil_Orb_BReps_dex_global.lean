-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_dex_global
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.dex_global
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:28.161726+00:00
-- url     : https://prove2.me/theorems/a1673562-7ef6-4ffe-a529-e6659750a1dc
-- title:
--   BReps: dex global
-- statement:
--   The BReps construction uses the dex global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/DexGlobal.lean#L11-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/DexGlobal.lean#L11-L199

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexBlockFrame
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module
variable {k : Type} [Field k]

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.dex_global {R : Type} [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R]
    {V : Type} [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V] :
    ∃ (M : Type) (_ : Fintype M) (L : M → Type) (_ : ∀ m, Fintype (L m)) (_ : ∀ m, Nonempty (L m))
      (Rc : R → (m : M) → L m → L m → k) (o : (m : M) → L m → k),
      ∀ N : V →ₗ[R] V, IsNilpotent N → ∀ v : V,
        ∃ (ι : M → Type) (_ : ∀ m, Fintype (ι m)) (l s : (m : M) → ι m → ℕ)
          (β : Basis (Σ m, L m × (Σ a : ι m, Fin (l m a))) k V),
          (∀ m a, 0 < l m a) ∧ (∀ m a, s m a ≤ l m a) ∧
          (∀ (z : R) m (p : L m) (j : Σ a : ι m, Fin (l m a)),
            z • β ⟨m, (p, j)⟩ = ∑ q, Rc z m p q • β ⟨m, (q, j)⟩) ∧
          (∀ m (p : L m) (a : ι m) (i : Fin (l m a)), N (β ⟨m, (p, ⟨a, i⟩)⟩) =
            if h : (i : ℕ) + 1 < l m a then β ⟨m, (p, ⟨a, ⟨i + 1, h⟩⟩)⟩ else 0) ∧
          v = ∑ m, ∑ p, ∑ a, (if h : s m a < l m a then o m p • β ⟨m, (p, ⟨a, ⟨s m a, h⟩⟩)⟩ else 0) ∧
          ∀ A : V →ₗ[R] V, A ∘ₗ N = N ∘ₗ A → ∀ m (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a →
            β.repr (A v) ⟨m, (p, ⟨a, i⟩)⟩ = 0 := by sorry
