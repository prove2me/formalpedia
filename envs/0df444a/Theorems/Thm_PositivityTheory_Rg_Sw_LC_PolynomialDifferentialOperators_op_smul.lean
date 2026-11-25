-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_smul
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:07.769329+00:00
-- url     : https://prove2.me/theorems/2a295679-fd8e-5788-b265-1b0b0b2d5cdc
-- title:
--   Polynomial Differential Operators: op smul
-- statement:
--   The Polynomial Differential Operators construction uses the op smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L94-L98

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

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_smul (a : ℂ) (u : Sym m n) (f : PX m n) : op (a • u) f = a • op u f := by sorry
