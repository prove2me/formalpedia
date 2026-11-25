-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_decomp
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.decomp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:48:58.887796+00:00
-- url     : https://prove2.me/theorems/c06fa46e-d658-44ec-bee6-723c2e0a55fc
-- title:
--   Polynomial Differential Operators: decomp
-- statement:
--   The Polynomial Differential Operators construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainInlInr.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainInlInr.lean#L121-L127

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ} {ε : Fin m → Bool}

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.decomp (t : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t.comapDomain Sum.inl Sum.inl_injective.injOn).mapDomain Sum.inl +
      (t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr = t := by sorry
