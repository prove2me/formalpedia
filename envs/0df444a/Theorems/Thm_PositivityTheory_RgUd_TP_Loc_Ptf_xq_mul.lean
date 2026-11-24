-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_xq_mul
-- name    : PositivityTheory.RgUd.TP.Loc.Ptf.xq_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:15.726958+00:00
-- url     : https://prove2.me/theorems/48527bd0-5eef-42e7-9791-f69af00febe8
-- title:
--   Ptf: xq mul
-- statement:
--   The Ptf construction uses the xq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean#L41-L42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Loc PositivityTheory.RgUd.TP.Loc.Ptf
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem PositivityTheory.RgUd.TP.Loc.Ptf.xq_mul (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x * y) = xq I x * xq I y := by sorry
