-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cd_affine
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_affine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:16.389565+00:00
-- url     : https://prove2.me/theorems/348fcb57-5892-4a69-bd11-0e3b77b20b6a
-- title:
--   GB: pb cd affine
-- statement:
--   The GB construction uses the pb cd affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L25-L29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_affine (a : ℂ) (e : ℂ) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (e * a) • b) i j) := by sorry
