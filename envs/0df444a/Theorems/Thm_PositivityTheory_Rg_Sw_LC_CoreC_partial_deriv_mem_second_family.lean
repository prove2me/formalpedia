-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_second_family
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.partial_deriv_mem_second_family
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:12.003958+00:00
-- url     : https://prove2.me/theorems/f99b293d-955f-43ae-8a65-54e6896283b7
-- title:
--   Core C: partial deriv mem second family
-- statement:
--   The Core C construction uses the partial deriv mem second family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L64-L65

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.partial_deriv_mem_second_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p ∈ F2 ε := by sorry
