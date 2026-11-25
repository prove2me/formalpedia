-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_dex_block_frame
-- name    : PositivityTheory.RgUd.T.Nil.Orb.BReps.dex_block_frame
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:17.741296+00:00
-- url     : https://prove2.me/theorems/7c8d69be-c77a-5e94-8e71-fcf6afa55b50
-- title:
--   BReps: dex block frame
-- statement:
--   The BReps construction uses the dex block frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/DexBlockFrame.lean#L11-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CompactOrbits/NilpotentOrbits/OrbitIntegrals/CentralizerRepresentatives/DexBlockFrame.lean#L11-L85

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_Normal
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexBlockFrame
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
variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

theorem PositivityTheory.RgUd.T.Nil.Orb.BReps.dex_block_frame (I : Ideal R) [I.IsMaximal] {L : Type} [Fintype L] (b : Basis L k (R ⧸ I))
    {W : Type} [AddCommGroup W] [Module R W] [Module k W] [IsScalarTower k R W] [FiniteDimensional k W]
    (hW : ∀ z ∈ I, ∀ y : W, z • y = 0) (N : W →ₗ[R] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (β : Basis (L × Σ a : ι, Fin (l a)) k W),
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧
      (∀ (z : R) (p : L) (j : Σ a : ι, Fin (l a)),
        z • β (p, j) = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • β (q, j)) ∧
      (∀ (p : L) (a : ι) (i : Fin (l a)), N (β (p, ⟨a, i⟩)) =
        if h : (i : ℕ) + 1 < l a then β (p, ⟨a, ⟨i + 1, h⟩⟩) else 0) ∧
      v = ∑ p, ∑ a, (if h : s a < l a then b.repr 1 p • β (p, ⟨a, ⟨s a, h⟩⟩) else 0) ∧
      ∀ A : W →ₗ[R] W, A ∘ₗ N = N ∘ₗ A → ∀ (p : L) (a : ι) (i : Fin (l a)), (i : ℕ) < s a →
        β.repr (A v) (p, ⟨a, i⟩) = 0 := by sorry
