-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_eq
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.G.gf_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:50.607019+00:00
-- url     : https://prove2.me/theorems/191e6009-4424-4a87-9e7a-85f59fd9ccef
-- title:
--   G: gf eq
-- statement:
--   The G construction uses the gf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BfSmulRight.lean#L16-L23

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

theorem PositivityTheory.Rg.Sw.LC.CoreC.G.gf_eq (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S) (hq : q.support ⊆ S) :
    gf w p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * w s := by sorry
