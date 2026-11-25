-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_inr_add
-- name    : PositivityTheory.Rg.Sw.LC.B1.inr_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:13.540148+00:00
-- url     : https://prove2.me/theorems/1e306ad1-c0af-4e76-b59f-7623bcff934a
-- title:
--   B1: inr add
-- statement:
--   The B1 construction uses the inr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L127-L130

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

theorem PositivityTheory.Rg.Sw.LC.B1.inr_add (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (k : σ) :
    ((t + Finsupp.mapDomain Sum.inl μ : σ ⊕ σ →₀ ℕ)) (Sum.inr k) = t (Sum.inr k) := by sorry
