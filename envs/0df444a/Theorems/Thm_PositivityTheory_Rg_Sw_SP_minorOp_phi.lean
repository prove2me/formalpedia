-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_minorOp_phi
-- name    : PositivityTheory.Rg.Sw.SP.minorOp_phi
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:47.959751+00:00
-- url     : https://prove2.me/theorems/a3d9873c-375c-4dd4-968e-f06fb1caa1b7
-- title:
--   SP: minor Op phi
-- statement:
--   The SP construction uses the minor Op phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L84-L89

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
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
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.minorOp_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (f : Pm (Polynomial ℂ) ρ) :
    minorOp s m b I J (phi b I J f) = (-(cMn s b)) ^ ρ • phi b I J (detE (alMn m b) f) := by sorry
