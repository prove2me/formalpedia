-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisGal_ml_re__19bb9b094bcf
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisGal_ml_re__19bb9b094bcf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:21.928296+00:00
-- url     : https://prove2.me/theorems/2052fd7e-d9f5-4167-b17e-0455fc9f9986
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Gal ml re  19bb9b094bcf: P2 M Global Theory Companion Theory Rg Eis Gal ml re  19bb9b094bcf
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Gal ml re  19bb9b094bcf construction uses the P2 M Global Theory Companion Theory Rg Eis Gal ml re  19bb9b094bcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L95-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L95-L95

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

theorem P2M_GlobalTheory_CompanionTheory_RgEisGal_ml_re__19bb9b094bcf : (ml N l).2.re = N - 1 - l.2.re := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisGal».«ml_re₂» := P2M_GlobalTheory_CompanionTheory_RgEisGal_ml_re__19bb9b094bcf
