-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_infinite_circle
-- name    : PositivityTheory.Rg.Sw.LVs.TC.infinite_circle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:27.597421+00:00
-- url     : https://prove2.me/theorems/d9d5ccd9-ef54-430c-a1fe-2a5f115bc4c1
-- title:
--   TC: infinite circle
-- statement:
--   The TC construction uses the infinite circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopCompB.lean#L33-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopCompB.lean#L33-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC

theorem PositivityTheory.Rg.Sw.LVs.TC.infinite_circle : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by sorry
