-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_smul_f
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_smul_f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:07.209054+00:00
-- url     : https://prove2.me/theorems/a3ecfbed-e2a3-4d89-ad4e-978c41f98380
-- title:
--   Polynomial Differential Operators: op smul f
-- statement:
--   The Polynomial Differential Operators construction uses the op smul f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L115-L118

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_smul_f (u : Sym m n) (a : ℂ) (f : PX m n) : op u (a • f) = a • op u f := by sorry
