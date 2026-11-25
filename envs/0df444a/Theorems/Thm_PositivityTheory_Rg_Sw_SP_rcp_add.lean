-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_rcp_add
-- name    : PositivityTheory.Rg.Sw.SP.rcp_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:21.934242+00:00
-- url     : https://prove2.me/theorems/48127d8c-c696-49c8-9486-e51cb9856883
-- title:
--   SP: rcp add
-- statement:
--   The SP construction uses the rcp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L66-L67

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.rcp_add {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T + U) := by sorry
