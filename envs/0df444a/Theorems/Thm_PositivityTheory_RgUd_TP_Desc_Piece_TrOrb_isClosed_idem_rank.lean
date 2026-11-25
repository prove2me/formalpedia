-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_isClosed_idem_rank
-- name    : PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.isClosed_idem_rank
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:15.472536+00:00
-- url     : https://prove2.me/theorems/1be2411b-f016-5dee-8ad2-7551c2a97cee
-- title:
--   Tr Orb: is Closed idem rank
-- statement:
--   The Tr Orb construction uses the is Closed idem rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbB.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/TrOrbB.lean#L21-L36

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

theorem PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.isClosed_idem_rank (n : ℕ) : IsClosed {P : Matrix (Fin N) (Fin N) k | P * P = P ∧ P.rank = n} := by sorry
