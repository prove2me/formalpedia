-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_exp_neg_I
-- name    : PositivityTheory.Rg.Sw.LVs.TC.exp_neg_I
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:09.411801+00:00
-- url     : https://prove2.me/theorems/fa9e2863-9a72-41ec-83f1-c22c7b12d438
-- title:
--   TC: exp neg I
-- statement:
--   The TC construction uses the exp neg I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean#L14-L15

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

theorem PositivityTheory.Rg.Sw.LVs.TC.exp_neg_I (t : ℂ) : Complex.exp (-t * Complex.I) = (Complex.exp (t * Complex.I))⁻¹ := by sorry
