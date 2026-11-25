-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_sum_right
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.G.bf_sum_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:53.087337+00:00
-- url     : https://prove2.me/theorems/8e476292-2239-5075-aab0-c2e37e61e3ef
-- title:
--   G: bf sum right
-- statement:
--   The G construction uses the bf sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L317-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L317-L322

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreC PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
variable (w : (τ →₀ ℕ) → ℂ)
variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw
omit hw

theorem PositivityTheory.Rg.Sw.LC.CoreC.G.bf_sum_right (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    bf w p (∑ i ∈ I, f i) = ∑ i ∈ I, bf w p (f i) := by sorry
