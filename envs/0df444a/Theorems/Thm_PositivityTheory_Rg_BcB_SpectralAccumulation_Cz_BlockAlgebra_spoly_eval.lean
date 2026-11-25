-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_spoly_eval
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.spoly_eval
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:03.893095+00:00
-- url     : https://prove2.me/theorems/17e02896-20db-4f9d-8111-99172e93a7ca
-- title:
--   Block Algebra: spoly eval
-- statement:
--   The Block Algebra construction uses the spoly eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean#L166-L172

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.spoly_eval (n : ℕ) (χ : ℕ → ℂ) (h : χ n = 1) (u : ℂ) :
    (spoly n χ).eval u = ∑ k ∈ Finset.range (n + 1), u ^ k * χ k := by sorry
