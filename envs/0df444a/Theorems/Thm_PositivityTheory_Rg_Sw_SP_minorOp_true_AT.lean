-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_minorOp_true_AT
-- name    : PositivityTheory.Rg.Sw.SP.minorOp_true_AT
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:03.491455+00:00
-- url     : https://prove2.me/theorems/9bffa9f3-2cec-4e5d-8ff2-ec4333cfdd63
-- title:
--   SP: minor Op true AT
-- statement:
--   The SP construction uses the minor Op true AT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L178-L184

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

theorem PositivityTheory.Rg.Sw.SP.minorOp_true_AT (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q : Fm n} (hQ : Q ∈ AT n) :
    minorOp s m true I J Q ∈ AT n := by sorry
