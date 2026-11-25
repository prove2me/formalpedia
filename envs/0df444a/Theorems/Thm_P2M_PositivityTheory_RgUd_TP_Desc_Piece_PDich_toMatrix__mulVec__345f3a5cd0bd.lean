-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgUd_TP_Desc_Piece_PDich_toMatrix__mulVec__345f3a5cd0bd
-- name    : P2M_PositivityTheory_RgUd_TP_Desc_Piece_PDich_toMatrix__mulVec__345f3a5cd0bd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:44.190727+00:00
-- url     : https://prove2.me/theorems/bbee668b-7155-4464-abc0-204c40c6f05e
-- title:
--   P2 M Positivity Theory Rg Ud TP Desc Piece PDich to Matrix  mul Vec  345f3a5cd0bd: P2 M Positivity Theory Rg Ud TP Desc Piece PDich to Matrix  mul Vec  345f3a5cd0bd
-- statement:
--   The P2 M Positivity Theory Rg Ud TP Desc Piece PDich to Matrix  mul Vec  345f3a5cd0bd construction uses the P2 M Positivity Theory Rg Ud TP Desc Piece PDich to Matrix  mul Vec  345f3a5cd0bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_ToMatrixMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
variable {k : Type} [Field k] {N : ℕ}

theorem P2M_PositivityTheory_RgUd_TP_Desc_Piece_PDich_toMatrix__mulVec__345f3a5cd0bd (f : (Fin N → k) →ₗ[k] (Fin N → k)) (v : Fin N → k) :
    LinearMap.toMatrix' f *ᵥ v = f v := by sorry

alias «PositivityTheory».«RgUd».«TP».«Desc».«Piece».«PDich».«toMatrix'_mulVec'» := P2M_PositivityTheory_RgUd_TP_Desc_Piece_PDich_toMatrix__mulVec__345f3a5cd0bd
