-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_mom_add
-- name    : PositivityTheory.Rg.Sw.LC.mom_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:11.294815+00:00
-- url     : https://prove2.me/theorems/1af55bf1-7ca8-48f4-9e36-cddbc2ad3365
-- title:
--   LC: mom add
-- statement:
--   The LC construction uses the mom add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableMonomial.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/IntegrableMonomial.lean#L86-L88

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
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

theorem PositivityTheory.Rg.Sw.LC.mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by sorry
