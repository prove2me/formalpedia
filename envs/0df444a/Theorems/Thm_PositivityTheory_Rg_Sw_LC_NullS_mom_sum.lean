-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_mom_sum
-- name    : PositivityTheory.Rg.Sw.LC.NullS.mom_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:45.562027+00:00
-- url     : https://prove2.me/theorems/7760d004-8de7-4456-aae5-e9e739b90dbc
-- title:
--   Null S: mom sum
-- statement:
--   The Null S construction uses the mom sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L34-L40

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

theorem PositivityTheory.Rg.Sw.LC.NullS.mom_sum (c : ℝ) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    mom c (∑ i ∈ s, f i) = ∑ i ∈ s, mom c (f i) := by sorry
