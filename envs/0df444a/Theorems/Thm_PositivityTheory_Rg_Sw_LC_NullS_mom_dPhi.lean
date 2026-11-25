-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_mom_dPhi
-- name    : PositivityTheory.Rg.Sw.LC.NullS.mom_dPhi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:04.54782+00:00
-- url     : https://prove2.me/theorems/6be81b89-3b0d-4971-8f84-9eeda5db5fd6
-- title:
--   Null S: mom d Phi
-- statement:
--   The Null S construction uses the mom d Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L104-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L104-L124

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.NullS.mom_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (P : PX m n) :
    mom c (pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P) = 0 := by sorry
