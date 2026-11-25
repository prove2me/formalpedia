-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_unitary
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_unitary
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:46.471551+00:00
-- url     : https://prove2.me/theorems/574ececa-4d9f-492c-9071-1661b25732e2
-- title:
--   Polynomial Weight Action: act unitary
-- statement:
--   The Polynomial Weight Action construction uses the act unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L322-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L322-L327

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (act (m := m) u : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] MvPolynomial (FinalTheorems m n) ℂ) =
      aeval (Sum.elim (fun x : Fin n × Fin m => ∑ j, C (u x.1 j) * (X (Sum.inl (j, x.2)) : MvPolynomial (FinalTheorems m n) ℂ))
        (fun y : Fin n × Fin m => ∑ j, C (star (u y.1 j)) * X (Sum.inr (j, y.2)))) := by sorry
