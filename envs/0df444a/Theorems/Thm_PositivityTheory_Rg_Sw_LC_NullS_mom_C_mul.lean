-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_mom_C_mul
-- name    : PositivityTheory.Rg.Sw.LC.NullS.mom_C_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:27.464632+00:00
-- url     : https://prove2.me/theorems/54f7649f-2009-4b44-8b7c-308c3068c3ee
-- title:
--   Null S: mom C mul
-- statement:
--   The Null S construction uses the mom C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/NullOperatorEvaluation.lean#L20-L25

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

theorem PositivityTheory.Rg.Sw.LC.NullS.mom_C_mul (c : ℝ) (a : ℂ) (P : PX m n) : mom c (C a * P) = a * mom c P := by sorry
