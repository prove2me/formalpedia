-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_diag_single_diag
-- name    : PositivityTheory.Rg.Sw.LVs.TC.diag_single_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:47.087499+00:00
-- url     : https://prove2.me/theorems/533f2e6e-99a7-4152-97d3-2d999e586302
-- title:
--   TC: diag single diag
-- statement:
--   The TC construction uses the diag single diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCMatC.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCMatC.lean#L14-L21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
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

theorem PositivityTheory.Rg.Sw.LVs.TC.diag_single_diag (u v : Fin n → ℂ) (r s : Fin n) (c : ℂ) :
    diagonal u * single r s c * diagonal v = single r s (u r * c * v s) := by sorry
