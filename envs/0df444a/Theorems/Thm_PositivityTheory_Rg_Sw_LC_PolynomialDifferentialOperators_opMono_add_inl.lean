-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_add_inl
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.opMono_add_inl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:35.073269+00:00
-- url     : https://prove2.me/theorems/9b564ee6-b12d-4c5f-879a-eaf39d2d8403
-- title:
--   Polynomial Differential Operators: op Mono add inl
-- statement:
--   The Polynomial Differential Operators construction uses the op Mono add inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L136-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L136-L145

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
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
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.opMono_add_inl (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inl k) 1) f = X k * opMono t f := by sorry
