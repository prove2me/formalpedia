-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_clsGainB_of
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.clsGainB_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:16.737241+00:00
-- url     : https://prove2.me/theorems/02d00eb1-9c24-51af-a33d-20ad349c49c5
-- title:
--   GB: cls Gain B of
-- statement:
--   The GB construction uses the cls Gain B of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContDiffHerm.lean#L22-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContDiffHerm.lean#L22-L73

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_RatBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContDiffHerm
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PositivityTheory.Rg.Sw.WR.K.GB.clsGainB_of (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by sorry
