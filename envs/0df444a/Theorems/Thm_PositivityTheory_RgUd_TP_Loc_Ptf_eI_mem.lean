-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_eI_mem
-- name    : PositivityTheory.RgUd.TP.Loc.Ptf.eI_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:14.725173+00:00
-- url     : https://prove2.me/theorems/e75b7376-eda3-4f54-9d4c-11fd803c5dd6
-- title:
--   Ptf: e I mem
-- statement:
--   The Ptf construction uses the e I mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean#L144-L145

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
open Classical
attribute [local instance] Ideal.Quotient.field
variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]

theorem PositivityTheory.RgUd.TP.Loc.Ptf.eI_mem {I J : MaximalSpectrum R} (h : J ≠ I) : eI I ∈ J.asIdeal := by sorry
