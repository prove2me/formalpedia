-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_an_fQ
-- name    : PositivityTheory.Rg.Sw.SP.an_fQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:41.117615+00:00
-- url     : https://prove2.me/theorems/c6116f8b-e47b-4c9b-8bd1-95afb536ec7d
-- title:
--   SP: an f Q
-- statement:
--   The SP construction uses the an f Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L15-L23

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.an_fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B₀ : MC n) (hB : B₀ ∈ OmS s) : AnalyticAt ℂ (fQ s z m Q) B₀ := by sorry
