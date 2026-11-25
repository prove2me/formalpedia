-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_goodT_add_inl
-- name    : PositivityTheory.Rg.Sw.LC.B1.goodT_add_inl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:20.127807+00:00
-- url     : https://prove2.me/theorems/34b9e7dc-e70b-4acb-83e4-bb8b6fcfbdbf
-- title:
--   B1: good T add inl
-- statement:
--   The B1 construction uses the good T add inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L206-L215

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)

theorem PositivityTheory.Rg.Sw.LC.B1.goodT_add_inl (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (ht : GoodT ε t) (hμ : ∀ k ∈ μ.support, inF1 ε k) :
    GoodT ε (Finsupp.mapDomain Sum.inl μ + t) := by sorry
