-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_lcp_smul
-- name    : PositivityTheory.Rg.Sw.SP.lcp_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:14.176284+00:00
-- url     : https://prove2.me/theorems/040bce5c-cece-493d-9a9f-06de6124be17
-- title:
--   SP: lcp smul
-- statement:
--   The SP construction uses the lcp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L100-L101

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

theorem PositivityTheory.Rg.Sw.SP.lcp_smul {Q' : Fm n} (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) : LCP Q' (c • T) := by sorry
