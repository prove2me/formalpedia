-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_X_mul
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.G.gf_X_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:00.393499+00:00
-- url     : https://prove2.me/theorems/9bac7e02-08d4-5f3e-9943-5fd1b4d7c776
-- title:
--   G: gf X mul
-- statement:
--   The G construction uses the gf X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L110-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L110-L129

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.G.gf_X_mul (k : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * p) q = κ * gf w p (pderiv k q) := by sorry
