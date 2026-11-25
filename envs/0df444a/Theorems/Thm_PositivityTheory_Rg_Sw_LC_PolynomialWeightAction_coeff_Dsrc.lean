-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_coeff_Dsrc
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.coeff_Dsrc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:58.496739+00:00
-- url     : https://prove2.me/theorems/a246fae0-05ce-46ba-a514-10f0c2392b2e
-- title:
--   Polynomial Weight Action: coeff Dsrc
-- statement:
--   The Polynomial Weight Action construction uses the coeff Dsrc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L263-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L263-L271

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.coeff_Dsrc (l : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ) (d : FinalTheorems m n →₀ ℕ) :
    coeff d (Dsrc (m := m) l l p) = ((wgt l d : ℤ) : ℂ) * coeff d p := by sorry
