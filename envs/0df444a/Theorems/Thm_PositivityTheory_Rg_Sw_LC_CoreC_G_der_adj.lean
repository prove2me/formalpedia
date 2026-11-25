-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_der_adj
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.G.der_adj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:19.097977+00:00
-- url     : https://prove2.me/theorems/ce22e3c9-a589-4154-b7b4-bfb0a5986096
-- title:
--   G: der adj
-- statement:
--   The G construction uses the der adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L214-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L214-L222

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.G.der_adj {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (D D' : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u)
    (hlin' : ∀ v, D' (X v) = ∑ u, (D' (X v)).coeff (Finsupp.single u 1) • X u)
    (htr : ∀ v u, (D' (X u)).coeff (Finsupp.single v 1) = star ((D (X v)).coeff (Finsupp.single u 1)))
    (p q : MvPolynomial τ ℂ) : gf w (D p) q = gf w p (D' q) := by sorry
