-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_eq
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.G.bf_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:25.242054+00:00
-- url     : https://prove2.me/theorems/f05a4488-0dd2-4aab-989a-81a02bca037d
-- title:
--   G: bf eq
-- statement:
--   The G construction uses the bf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L227-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L227-L234

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.G.bf_eq (w : (τ →₀ ℕ) → ℂ) (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S)
    (hq : q.support ⊆ S) : bf w p q = ∑ s ∈ S, p.coeff s * q.coeff s * w s := by sorry
