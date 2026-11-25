-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_neg_right
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.G.gf_neg_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:44.755546+00:00
-- url     : https://prove2.me/theorems/99c38cb8-8892-55ba-af8b-5434fce893d4
-- title:
--   G: gf neg right
-- statement:
--   The G construction uses the gf neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L64-L65

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.G.gf_neg_right (p q : MvPolynomial τ ℂ) : gf w p (-q) = -gf w p q := by sorry
