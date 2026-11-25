-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_comp
-- name    : PositivityTheory.Rg.Sw.SP.lcp_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:26.553996+00:00
-- url     : https://prove2.me/theorems/a4ce7db4-00c6-4917-82f3-df5b98a3b9f3
-- title:
--   SP: lcp comp
-- statement:
--   The SP construction uses the lcp comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L94-L95

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

theorem PositivityTheory.Rg.Sw.SP.lcp_comp {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T ∘ₗ U) := by sorry
