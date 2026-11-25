-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_divZ_mono
-- name    : PositivityTheory.Rg.Sw.SP.divZ_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:03.476337+00:00
-- url     : https://prove2.me/theorems/9be59319-0421-538a-9244-90e7e7bed7ed
-- title:
--   SP: div Z mono
-- statement:
--   The SP construction uses the div Z mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDiv.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDiv.lean#L32-L33

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDiv
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

theorem PositivityTheory.Rg.Sw.SP.divZ_mono {i j : ℕ} {Q : Fm n} (hQ : DivZ i Q) (h : j ≤ i) : DivZ j Q := by sorry
