-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_dA_ne
-- name    : PositivityTheory.Rg.Sw.LVs.TC.dA_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:10.605697+00:00
-- url     : https://prove2.me/theorems/516309a0-780d-4c09-ae3f-10711dd5eb1b
-- title:
--   TC: d A ne
-- statement:
--   The TC construction uses the d A ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean#L31-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.TC.dA_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dA j θ a ≠ 0 := by sorry
