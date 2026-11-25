-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_pderiv_true_AT
-- name    : PositivityTheory.Rg.Sw.SP.pderiv_true_AT
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:17.348869+00:00
-- url     : https://prove2.me/theorems/190b878b-48d1-43aa-8ea3-4a079ddf0007
-- title:
--   SP: pderiv true AT
-- statement:
--   The SP construction uses the pderiv true AT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L143-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L143-L156

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

theorem PositivityTheory.Rg.Sw.SP.pderiv_true_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (true, a, d) Q ∈ AT n := by sorry
