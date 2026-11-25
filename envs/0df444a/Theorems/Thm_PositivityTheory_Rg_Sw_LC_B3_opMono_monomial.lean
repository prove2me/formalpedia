-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_opMono_monomial
-- name    : PositivityTheory.Rg.Sw.LC.B3.opMono_monomial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:55.214632+00:00
-- url     : https://prove2.me/theorems/9758ece7-3400-4125-8e6c-65db90db4311
-- title:
--   B3: op Mono monomial
-- statement:
--   The B3 construction uses the op Mono monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L314-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean#L314-L324

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.B3.opMono_monomial (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (γ : Fin m × Fin n × Bool →₀ ℕ) :
    opMono t (monomial γ 1 : PX m n) =
      monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn + (γ - ∑ k, Finsupp.single k (t (Sum.inr k))))
        (∏ k, ((γ k).descFactorial (t (Sum.inr k)) : ℂ)) := by sorry
