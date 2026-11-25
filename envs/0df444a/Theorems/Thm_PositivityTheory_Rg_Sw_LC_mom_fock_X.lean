-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_fock_X
-- name    : PositivityTheory.Rg.Sw.LC.mom_fock_X
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:09.728207+00:00
-- url     : https://prove2.me/theorems/36430040-b75a-4ac7-a06a-7c42c2e738dc
-- title:
--   LC: mom fock X
-- statement:
--   The LC construction uses the mom fock X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FockMomOfBasic.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FockMomOfBasic.lean#L52-L59

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMomOfBasic
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
variable (hM : OneMom)
include hB hM

theorem PositivityTheory.Rg.Sw.LC.mom_fock_X (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    mom c (fock c (X k * p)) = (2 * c : ℂ) * mom c (fock c (pderiv (flip k) p)) := by sorry
