-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_Dsrc_diag_X
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.Dsrc_diag_X
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:26.605812+00:00
-- url     : https://prove2.me/theorems/8041d546-cd6d-442a-bf7b-11baa29598ba
-- title:
--   Polynomial Weight Action: Dsrc diag X
-- statement:
--   The Polynomial Weight Action construction uses the Dsrc diag X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L226-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean#L226-L236

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.Dsrc_diag_X (l : Fin n) (v : FinalTheorems m n) :
    Dsrc (m := m) l l (X v) = C ((wgt l (Finsupp.single v 1) : ℤ) : ℂ) * X v := by sorry
