-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_T1
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.T1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:05.974497+00:00
-- url     : https://prove2.me/theorems/4ec610e8-c004-49d6-a8a0-1b0a59cf1b46
-- title:
--   Core C: T1
-- statement:
--   The Core C construction uses the T1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L198-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L198-L204

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.T1 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X k * h * g) = ((2 * c : ℝ) : ℂ) * contr c (h * pderiv (pE k) g) := by sorry
