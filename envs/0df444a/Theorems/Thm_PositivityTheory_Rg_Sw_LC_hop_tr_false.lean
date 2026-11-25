-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_tr_false
-- name    : PositivityTheory.Rg.Sw.LC.hop_tr_false
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:45.492898+00:00
-- url     : https://prove2.me/theorems/ed63234e-ebd1-4995-a8f4-bb8f74352e1e
-- title:
--   LC: hop tr false
-- statement:
--   The LC construction uses the hop tr false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L107-L113

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
include hB

theorem PositivityTheory.Rg.Sw.LC.hop_tr_false {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, false) * fock c q) = fock c (X (a, i, true) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, false) q) := by sorry
