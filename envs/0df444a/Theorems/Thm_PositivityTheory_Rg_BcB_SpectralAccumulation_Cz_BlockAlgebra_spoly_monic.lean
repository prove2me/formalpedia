-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_spoly_monic
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.spoly_monic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:09.028597+00:00
-- url     : https://prove2.me/theorems/a7f091a8-6f4d-48f2-bea1-12d144b8be56
-- title:
--   Block Algebra: spoly monic
-- statement:
--   The Block Algebra construction uses the spoly monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L158-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L158-L159

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.spoly_monic (n : ℕ) (χ : ℕ → ℂ) : (spoly n χ).Monic := by sorry
