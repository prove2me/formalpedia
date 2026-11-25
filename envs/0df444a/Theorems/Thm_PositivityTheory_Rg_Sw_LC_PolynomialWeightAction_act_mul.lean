-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_mul
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:59.551804+00:00
-- url     : https://prove2.me/theorems/8c41d3ba-cb53-4327-a09a-df65143b5674
-- title:
--   Polynomial Weight Action: act mul
-- statement:
--   The Polynomial Weight Action construction uses the act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L108-L110

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_mul (A B : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (FinalTheorems m n) ℂ) :
    act (A * B) q = act B (act A q) := by sorry
