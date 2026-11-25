-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_trace_comp_smulRight
-- name    : PositivityTheory.RgUd.TP.Loc.Ptf.trace_comp_smulRight
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:24.527588+00:00
-- url     : https://prove2.me/theorems/031ab2fc-c0c7-565c-a557-ee9eeff370f8
-- title:
--   Ptf: trace comp smul Right
-- statement:
--   The Ptf construction uses the trace comp smul Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean#L63-L72

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

theorem PositivityTheory.RgUd.TP.Loc.Ptf.trace_comp_smulRight {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : W →ₗ[K] W) (φ : Module.Dual K W) (w : W) : LinearMap.trace K W (f * φ.smulRight w) = φ (f w) := by sorry
