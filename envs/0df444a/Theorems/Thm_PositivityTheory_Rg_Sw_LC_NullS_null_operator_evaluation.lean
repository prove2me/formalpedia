-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_null_operator_evaluation
-- name    : PositivityTheory.Rg.Sw.LC.NullS.null_operator_evaluation
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:52.080323+00:00
-- url     : https://prove2.me/theorems/d011aede-f39e-54e0-ad26-50e9e184f826
-- title:
--   Null S: null operator evaluation
-- statement:
--   The Null S construction uses the null operator evaluation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L89-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L89-L102

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

theorem PositivityTheory.Rg.Sw.LC.NullS.null_operator_evaluation (c : ℝ) (P : PX m n) (k : Fin m × Fin n × Bool) (z : ℂ) :
    Qv c P (ev1 k z) = C z * (pderiv (k.1, k.2.1, false) P + P * pderiv (k.1, k.2.1, false) (Sg c)) +
      C (star z) * (pderiv (k.1, k.2.1, true) P + P * pderiv (k.1, k.2.1, true) (Sg c)) := by sorry
