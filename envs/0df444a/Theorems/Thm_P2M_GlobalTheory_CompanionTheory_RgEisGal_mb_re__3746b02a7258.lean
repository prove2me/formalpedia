-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgEisGal_mb_re__3746b02a7258
-- name    : P2M_GlobalTheory_CompanionTheory_RgEisGal_mb_re__3746b02a7258
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:18.48781+00:00
-- url     : https://prove2.me/theorems/493e06ec-fdf5-412a-85bc-8d107f4cd153
-- title:
--   P2 M Global Theory Companion Theory Rg Eis Gal mb re  3746b02a7258: P2 M Global Theory Companion Theory Rg Eis Gal mb re  3746b02a7258
-- statement:
--   The P2 M Global Theory Companion Theory Rg Eis Gal mb re  3746b02a7258 construction uses the P2 M Global Theory Companion Theory Rg Eis Gal mb re  3746b02a7258 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GalleryOfTubesAndCrossing.lean#L90-L91

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

theorem P2M_GlobalTheory_CompanionTheory_RgEisGal_mb_re__3746b02a7258 : (mb N l).2.re = 2 * N - 1 - l.1.re - l.2.re := by sorry

alias «GlobalTheory».«CompanionTheory».«RgEisGal».«mb_re₂» := P2M_GlobalTheory_CompanionTheory_RgEisGal_mb_re__3746b02a7258
