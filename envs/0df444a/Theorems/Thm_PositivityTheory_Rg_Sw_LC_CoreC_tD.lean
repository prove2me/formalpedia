-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_tD
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.tD
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:35.515883+00:00
-- url     : https://prove2.me/theorems/c5bb2250-3dc7-4a37-b3e5-02859a53cb68
-- title:
--   Core C: t D
-- statement:
--   The Core C construction uses the t D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContractionFirstOperatorAdjoint.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContractionFirstOperatorAdjoint.lean#L41-L49

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContractionFirstOperatorAdjoint
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

theorem PositivityTheory.Rg.Sw.LC.CoreC.tD (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) ^ 2 * contr c (pderiv (b, i, false) (pderiv (a, i, true) h) * g) =
      contr c (h * (X (a, i, false) * X (b, i, true) * g)) := by sorry
