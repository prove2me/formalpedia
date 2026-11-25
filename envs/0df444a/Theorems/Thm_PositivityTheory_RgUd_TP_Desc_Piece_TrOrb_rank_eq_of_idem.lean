-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_rank_eq_of_idem
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.rank_eq_of_idem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:17.029631+00:00
-- url     : https://prove2.me/theorems/9c75aeee-4445-4142-aa16-863ec55e614e
-- title:
--   Tr Orb: rank eq of idem
-- statement:
--   The Tr Orb construction uses the rank eq of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbB.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbB.lean#L11-L19

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbB
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
variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}

theorem PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.rank_eq_of_idem {R : Type*} [Field R] {P Q : Matrix (Fin N) (Fin N) R} (hP : P * P = P) (hQ : Q * Q = Q)
    (hu : IsUnit (Q * P + (1 - Q) * (1 - P)).det) : P.rank = Q.rank := by sorry
