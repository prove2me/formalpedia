-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__720713fbd4c6
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__720713fbd4c6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:38.271811+00:00
-- url     : https://prove2.me/theorems/cc84988e-8ddf-4cbb-8805-5414d491ec6d
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Gal mc re  720713fbd4c6: P2 M Global Theory Companion Theory Rg Eis Gal mc re  720713fbd4c6
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Gal mc re  720713fbd4c6 construction uses the P2 M Global Theory Companion Theory Rg Eis Gal mc re  720713fbd4c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L85-L85

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable (N : ℝ) (l : ℂ × ℂ)

theorem P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__720713fbd4c6 : (mc N l).2.re = l.2.re + 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisGal».«mc_re₂» := P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__720713fbd4c6
