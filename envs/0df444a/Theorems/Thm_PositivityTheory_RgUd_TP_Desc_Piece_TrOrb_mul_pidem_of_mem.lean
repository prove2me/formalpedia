-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_mul_pidem_of_mem
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.mul_pidem_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:21.774715+00:00
-- url     : https://prove2.me/theorems/01fa8da4-f926-5634-bd62-e31f2b490384
-- title:
--   Tr Orb: mul pidem of mem
-- statement:
--   The Tr Orb construction uses the mul pidem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbA.lean#L84-L91

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.mul_pidem_of_mem (I : MaximalSpectrum A) {x : A} (hx : x ∈ I.asIdeal) : x * pidem A I = 0 := by sorry
