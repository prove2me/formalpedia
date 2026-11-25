-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_divZ_mul
-- name    : PositivityTheory.Rg.Sw.SP.divZ_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:15.098748+00:00
-- url     : https://prove2.me/theorems/cd683428-9428-42ca-8c02-2fe3b7dd4c20
-- title:
--   SP: div Z mul
-- statement:
--   The SP construction uses the div Z mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L34-L39

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

theorem PositivityTheory.Rg.Sw.SP.divZ_mul {i j : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ j Q) : DivZ (i + j) (P * Q) := by sorry
