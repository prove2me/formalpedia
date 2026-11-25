-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_decomp
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.decomp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:34.486849+00:00
-- url     : https://prove2.me/theorems/20ba21f1-23d4-4f5e-baae-510164e582ca
-- title:
--   Block Algebra: decomp
-- statement:
--   The Block Algebra construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L298-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L298-L479

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.decomp {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] (r s : ℕ)
    (A B : ι → ℕ → Module.End ℂ V) (m : ι → Multiset ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hAW : ∀ i k, ∀ w ∈ W, A i k w ∈ W) (hBW : ∀ i k, ∀ w ∈ W, B i k w ∈ W)
    (hAA : ∀ i k j l, ∀ w ∈ W, A i k (A j l w) = A j l (A i k w))
    (hAB : ∀ i k j l, ∀ w ∈ W, A i k (B j l w) = B j l (A i k w))
    (hBB : ∀ i k j l, ∀ w ∈ W, B i k (B j l w) = B j l (B i k w))
    (hA1 : ∀ i, ∀ w ∈ W, A i r w = w) (hB1 : ∀ i, ∀ w ∈ W, B i s w = w)
    (hm : ∀ i, (m i).Nodup) (v : V) (hv : v ∈ W)
    (hrel : ∀ i (u : ℂ), (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) ((∑ l ∈ Finset.range (s + 1), u ^ l • B i l) v) =
      ((m i).map (u + ·)).prod • v) :
    ∃ (S : Finset (ι → Multiset ℂ)) (x : (ι → Multiset ℂ) → V), (∀ σ ∈ S, x σ ∈ W) ∧ v = ∑ σ ∈ S, x σ ∧
      ∀ σ ∈ S, ∀ i, σ i ≤ m i ∧ Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (x σ) = ((σ i).map (u + ·)).prod • x σ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (x σ) = ((m i - σ i).map (u + ·)).prod • x σ := by sorry
