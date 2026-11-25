-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_nondeg
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.nondeg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:55.456907+00:00
-- url     : https://prove2.me/theorems/b62db631-37d4-525f-93d9-2d1082df61d6
-- title:
--   Core C: nondeg
-- statement:
--   The Core C construction uses the nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SecondOperatorMemSecondFamily.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SecondOperatorMemSecondFamily.lean#L49-L59

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SecondOperatorMemSecondFamily
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

theorem PositivityTheory.Rg.Sw.LC.CoreC.nondeg (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {h : PX m n} (hh : h ∈ F1 ε)
    (h0 : ∀ u : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ u.support, ¬ inF1 ε k) → contr c (h * monomial u 1) = 0) : h = 0 := by sorry
