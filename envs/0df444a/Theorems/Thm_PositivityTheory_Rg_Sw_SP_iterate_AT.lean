-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_iterate_AT
-- name    : PositivityTheory.Rg.Sw.SP.iterate_AT
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:39.568372+00:00
-- url     : https://prove2.me/theorems/db68536a-71fc-506c-8ab7-3f784322e1c3
-- title:
--   SP: iterate AT
-- statement:
--   The SP construction uses the iterate AT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L186-L190

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

theorem PositivityTheory.Rg.Sw.SP.iterate_AT {T : Fm n →ₗ[ℂ] Fm n} (hT : ∀ Q, Q ∈ AT n → T Q ∈ AT n) (N : ℕ) {Q : Fm n} (hQ : Q ∈ AT n) :
    T^[N] Q ∈ AT n := by sorry
