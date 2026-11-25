-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_comp
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:48.449631+00:00
-- url     : https://prove2.me/theorems/2eed002e-e31f-452c-82a7-2b7b1886cbfb
-- title:
--   Polynomial Weight Action: act comp
-- statement:
--   The Polynomial Weight Action construction uses the act comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L94-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L94-L106

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_comp (A B : Matrix (Fin n) (Fin n) ℂ) :
    act (m := m) (B * A) = (act A).comp (act B) := by sorry
