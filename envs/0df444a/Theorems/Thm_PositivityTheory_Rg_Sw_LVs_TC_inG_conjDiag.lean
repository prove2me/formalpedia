-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_inG_conjDiag
-- name    : PositivityTheory.Rg.Sw.LVs.TC.inG_conjDiag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:51:32.175005+00:00
-- url     : https://prove2.me/theorems/86a9570a-7e2d-45fe-ac21-bb5405da222a
-- title:
--   TC: in G conj Diag
-- statement:
--   The TC construction uses the in G conj Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCMatC.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCMatC.lean#L23-L38

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

theorem PositivityTheory.Rg.Sw.LVs.TC.inG_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, star (d1 a) * d1 a = 1) (h2 : ∀ a, star (d2 a) * d2 a = 1) :
    InG (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n) := by sorry
