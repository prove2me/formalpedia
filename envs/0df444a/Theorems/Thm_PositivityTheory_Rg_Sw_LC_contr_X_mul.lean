-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_X_mul
-- name    : PositivityTheory.Rg.Sw.LC.contr_X_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:02.725906+00:00
-- url     : https://prove2.me/theorems/ccc353b8-e168-581e-9e0d-432ba9f87152
-- title:
--   LC: contr X mul
-- statement:
--   The LC construction uses the contr X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L102-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L102-L110

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
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

theorem PositivityTheory.Rg.Sw.LC.contr_X_mul (c : ℝ) (k : Fin m × Fin n × Bool) (p : PX m n) :
    contr c (X k * p) = (2 * c : ℂ) * contr c (pderiv (flip k) p) := by sorry
