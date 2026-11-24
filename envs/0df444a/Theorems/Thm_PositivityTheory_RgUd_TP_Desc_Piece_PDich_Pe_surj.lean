-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_Pe_surj
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.PDich.Pe_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:45.945017+00:00
-- url     : https://prove2.me/theorems/aa658ade-1205-4e22-90c8-000a68601d06
-- title:
--   PDich: Pe surj
-- statement:
--   The PDich construction uses the Pe surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/ToMatrixMulVec.lean#L52-L52

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
variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

theorem PositivityTheory.RgUd.TP.Desc.Piece.PDich.Pe_surj (e : Matrix (Fin N) (Fin N) k) : Function.Surjective (Pe e) := by sorry
