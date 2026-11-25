-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_deriv_part
-- name    : PositivityTheory.Rg.Sw.SP.deriv_part
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:39.875222+00:00
-- url     : https://prove2.me/theorems/1700e133-babf-40ba-a144-46ed817cd9e4
-- title:
--   SP: deriv part
-- statement:
--   The SP construction uses the deriv part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L25-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L25-L57

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
set_option maxHeartbeats 2000000

theorem PositivityTheory.Rg.Sw.SP.deriv_part (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) = phi b I J (del p q f) := by sorry
