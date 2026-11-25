-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_apply_eig
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.apply_eig
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:24.694522+00:00
-- url     : https://prove2.me/theorems/f372c099-524e-5d78-b335-0a35829cb0ce
-- title:
--   Block Algebra: apply eig
-- statement:
--   The Block Algebra construction uses the apply eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L149-L154

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.apply_eig (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (y : M)
    (hy : ∀ k ∈ Finset.range (n + 1), a k y = χ k • y) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) y = (∑ k ∈ Finset.range (n + 1), u ^ k * χ k) • y := by sorry
