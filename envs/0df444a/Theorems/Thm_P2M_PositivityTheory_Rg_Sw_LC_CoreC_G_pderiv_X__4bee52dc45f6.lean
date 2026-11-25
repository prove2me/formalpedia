-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreC_G_pderiv_X__4bee52dc45f6
-- name    : P2M_PositivityTheory_Rg_Sw_LC_CoreC_G_pderiv_X__4bee52dc45f6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:52.652417+00:00
-- url     : https://prove2.me/theorems/1239bfa0-30ff-4376-9301-b6371bd68a38
-- title:
--   P2 M Positivity Theory Rg Sw LC Core C G pderiv X  4bee52dc45f6: P2 M Positivity Theory Rg Sw LC Core C G pderiv X  4bee52dc45f6
-- statement:
--   The P2 M Positivity Theory Rg Sw LC Core C G pderiv X  4bee52dc45f6 construction uses the P2 M Positivity Theory Rg Sw LC Core C G pderiv X  4bee52dc45f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L185-L188

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
omit [Fintype τ]

theorem P2M_PositivityTheory_Rg_Sw_LC_CoreC_G_pderiv_X__4bee52dc45f6 (v u : τ) : pderiv v (X u : MvPolynomial τ ℂ) = if v = u then 1 else 0 := by sorry

alias «PositivityTheory».«Rg».«Sw».«LC».«CoreC».«G».«pderiv_X'» := P2M_PositivityTheory_Rg_Sw_LC_CoreC_G_pderiv_X__4bee52dc45f6
