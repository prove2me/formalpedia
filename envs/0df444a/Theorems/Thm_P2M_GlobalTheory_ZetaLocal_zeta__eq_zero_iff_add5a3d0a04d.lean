-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaLocal_zeta__eq_zero_iff_add5a3d0a04d
-- name    : P2M_GlobalTheory_ZetaLocal_zeta__eq_zero_iff_add5a3d0a04d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:57.981121+00:00
-- url     : https://prove2.me/theorems/05ce1283-b105-428c-96a0-5fc3ce10dd34
-- title:
--   P2 M Global Theory Zeta Local zeta  eq zero iff add5a3d0a04d: P2 M Global Theory Zeta Local zeta  eq zero iff add5a3d0a04d
-- statement:
--   The P2 M Global Theory Zeta Local zeta  eq zero iff add5a3d0a04d construction uses the P2 M Global Theory Zeta Local zeta  eq zero iff add5a3d0a04d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaLocal

theorem P2M_GlobalTheory_ZetaLocal_zeta__eq_zero_iff_add5a3d0a04d (w : ℂ) : riemannZeta₁ w = 0 ↔ w ≠ 1 ∧ riemannZeta w = 0 := by sorry

alias «GlobalTheory».«ZetaLocal».«zeta₁_eq_zero_iff» := P2M_GlobalTheory_ZetaLocal_zeta__eq_zero_iff_add5a3d0a04d
