-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_true_AT
-- name    : PositivityTheory.Rg.Sw.SP.opH_true_AT
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:12.057614+00:00
-- url     : https://prove2.me/theorems/85487a0f-18ae-55ba-8c53-55309a6b82b2
-- title:
--   SP: op H true AT
-- statement:
--   The SP construction uses the op H true AT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L164-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L164-L170

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

theorem PositivityTheory.Rg.Sw.SP.opH_true_AT (s : ℂ) (m : ℕ) (k l : Fin n) {Q : Fm n} (hQ : Q ∈ AT n) : opH s m true k l Q ∈ AT n := by sorry
