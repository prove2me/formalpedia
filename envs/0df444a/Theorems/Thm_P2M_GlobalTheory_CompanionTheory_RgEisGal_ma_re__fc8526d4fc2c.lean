-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisGal_ma_re__fc8526d4fc2c
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisGal_ma_re__fc8526d4fc2c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:06.177511+00:00
-- url     : https://prove2.me/theorems/e4b28483-fc43-4d0c-b039-d27c212c8e2f
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Gal ma re  fc8526d4fc2c: P2 M Global Theory Companion Theory Rg Eis Gal ma re  fc8526d4fc2c
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Gal ma re  fc8526d4fc2c construction uses the P2 M Global Theory Companion Theory Rg Eis Gal ma re  fc8526d4fc2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L88-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L88-L88

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

theorem P2M_GlobalTheory_CompanionTheory_RgEisGal_ma_re__fc8526d4fc2c : (ma N l).2.re = l.2.re + 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisGal».«ma_re₂» := P2M_GlobalTheory_CompanionTheory_RgEisGal_ma_re__fc8526d4fc2c
