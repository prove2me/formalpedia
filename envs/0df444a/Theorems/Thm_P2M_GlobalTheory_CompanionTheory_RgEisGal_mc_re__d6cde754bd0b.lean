-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__d6cde754bd0b
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__d6cde754bd0b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:56.234132+00:00
-- url     : https://prove2.me/theorems/70abab01-0a66-46e1-9629-c3bcb199de88
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Gal mc re  d6cde754bd0b: P2 M Global Theory Companion Theory Rg Eis Gal mc re  d6cde754bd0b
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Gal mc re  d6cde754bd0b construction uses the P2 M Global Theory Companion Theory Rg Eis Gal mc re  d6cde754bd0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L83-L84

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

theorem P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__d6cde754bd0b : (mc N l).1.re = l.1.re + l.2.re + 1 - N := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisGal».«mc_re₁» := P2M_GlobalTheory_CompanionTheory_RgEisGal_mc_re__d6cde754bd0b
