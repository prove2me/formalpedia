-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_isUnit_poly
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.isUnit_poly
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:53.550289+00:00
-- url     : https://prove2.me/theorems/8392611e-e809-491b-a415-ad1e728f414f
-- title:
--   Block Algebra: is Unit poly
-- statement:
--   The Block Algebra construction uses the is Unit poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L122-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L122-L137

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.isUnit_poly (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (hcomm : ∀ k l, Commute (a k) (a l))
    (hnil : ∀ k, IsNilpotent (a k - χ k • 1)) (w : ℂ) (hw : (∑ k ∈ Finset.range (n + 1), w ^ k * χ k) ≠ 0) :
    IsUnit (∑ k ∈ Finset.range (n + 1), w ^ k • a k) := by sorry
