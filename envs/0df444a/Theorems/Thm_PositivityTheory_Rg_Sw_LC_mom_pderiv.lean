-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_pderiv
-- name    : PositivityTheory.Rg.Sw.LC.mom_pderiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:03.424806+00:00
-- url     : https://prove2.me/theorems/4f75f49f-b2eb-495b-87ae-28c16e59f8ff
-- title:
--   LC: mom pderiv
-- statement:
--   The LC construction uses the mom pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/GaussianMomentRecurrence.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/GaussianMomentRecurrence.lean#L77-L85

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hM : OneMom)
include hM

theorem PositivityTheory.Rg.Sw.LC.mom_pderiv (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by sorry
