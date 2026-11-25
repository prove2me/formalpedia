-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_mom_mul_dPhi
-- name    : PositivityTheory.Rg.Sw.LC.NullS.mom_mul_dPhi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:05.977425+00:00
-- url     : https://prove2.me/theorems/896173df-e06d-4096-ad25-8e46a4e0964f
-- title:
--   Null S: mom mul d Phi
-- statement:
--   The Null S construction uses the mom mul d Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L25-L33

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.NullS.mom_mul_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (U P : PX m n) :
    mom c (U * dPhi c k P) = -mom c (pderiv k U * P) := by sorry
