-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_piece
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.piece
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:59.507131+00:00
-- url     : https://prove2.me/theorems/76bd746b-f4b3-467d-9502-3465049c9f67
-- title:
--   Block Algebra: piece
-- statement:
--   The Block Algebra construction uses the piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L174-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L174-L292

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.piece [Nontrivial M] (r s : ℕ) (a b : ℕ → Module.End ℂ M) (haa : ∀ k l, Commute (a k) (a l))
    (hab : ∀ k l, Commute (a k) (b l)) (hbb : ∀ k l, Commute (b k) (b l))
    (ha : a r = 1) (hb : b s = 1) (m : Multiset ℂ) (hm : m.Nodup)
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
      (m.map (u + ·)).prod • (1 : Module.End ℂ M))
    (χa χb : ℕ → ℂ) (hna : ∀ k, IsNilpotent (a k - χa k • 1)) (hnb : ∀ l, IsNilpotent (b l - χb l • 1)) :
    ∃ σ : Multiset ℂ, σ ≤ m ∧ Multiset.card σ = r ∧ ∀ u : ℂ,
      (∑ k ∈ Finset.range (r + 1), u ^ k • a k) = (σ.map (u + ·)).prod • 1 ∧
      (∑ l ∈ Finset.range (s + 1), u ^ l • b l) = ((m - σ).map (u + ·)).prod • 1 := by sorry
