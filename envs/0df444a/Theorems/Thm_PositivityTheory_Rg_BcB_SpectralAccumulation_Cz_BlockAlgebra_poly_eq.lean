-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_poly_eq
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.poly_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:41.732252+00:00
-- url     : https://prove2.me/theorems/32bb3f1d-7d79-5c26-b911-2fba64f7a77b
-- title:
--   Block Algebra: poly eq
-- statement:
--   The Block Algebra construction uses the poly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L69-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L69-L120

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.poly_eq (n : ℕ) (a : ℕ → Module.End ℂ M) (ha : a n = 1) (σ : Multiset ℂ) (hσ : σ.Nodup)
    (hc : Multiset.card σ = n) (h : ∀ x ∈ σ, (∑ k ∈ Finset.range (n + 1), (-x) ^ k • a k) = 0) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) = (σ.map (u + ·)).prod • (1 : Module.End ℂ M) := by sorry
