-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
-- name    : P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:27.099806+00:00
-- url     : https://prove2.me/theorems/39764440-b1a3-47d5-9572-9840c0cc0024
-- title:
--   P2 M Global Theory Formal Calc pderiv subst  7084ce132710: P2 M Global Theory Formal Calc pderiv subst  7084ce132710
-- statement:
--   The P2 M Global Theory Formal Calc pderiv subst  7084ce132710 construction uses the P2 M Global Theory Formal Calc pderiv subst  7084ce132710 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalLogEqSumOfMultiplicativeParam.lean#L39-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]

theorem P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710 [Fintype ι] {a : ι → MvPowerSeries κ A}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι A) (j : κ) :
    pderiv A j (subst a f) = ∑ i, subst a (pderiv A i f) * pderiv A j (a i) := by sorry

alias «GlobalTheory».«FormalCalc».«pderiv_subst'» := P2M_GlobalTheory_FormalCalc_pderiv_subst__7084ce132710
