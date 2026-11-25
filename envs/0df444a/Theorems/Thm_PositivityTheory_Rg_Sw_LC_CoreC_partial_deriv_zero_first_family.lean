-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_zero_first_family
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.partial_deriv_zero_first_family
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:27.295654+00:00
-- url     : https://prove2.me/theorems/cacc73ee-8d12-5de0-841e-5bfd7e5a9eb1
-- title:
--   Core C: partial deriv zero first family
-- statement:
--   The Core C construction uses the partial deriv zero first family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L73-L77

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.partial_deriv_zero_first_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p = 0 := by sorry
