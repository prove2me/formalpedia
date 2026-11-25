-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_list_dv_mul
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.list_dv_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:29.697341+00:00
-- url     : https://prove2.me/theorems/59d0184e-09ad-5336-b3ee-a8034642d851
-- title:
--   Polynomial Differential Operators: list dv mul
-- statement:
--   The Polynomial Differential Operators construction uses the list dv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L35-L55

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.list_dv_mul (l : List (Ix m n)) (a b : Ix m n → ℕ) :
    (l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod = (l.map fun k => Dk k ^ (a k + b k)).prod := by sorry
