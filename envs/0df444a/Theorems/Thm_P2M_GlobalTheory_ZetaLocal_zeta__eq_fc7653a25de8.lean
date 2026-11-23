-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8
-- name    : P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:58.600487+00:00
-- url     : https://prove2.me/theorems/fa2cb1b8-9cac-415b-abf6-7413c8265fe2
-- title:
--   P2 M Global Theory Zeta Local zeta  eq fc7653a25de8: P2 M Global Theory Zeta Local zeta  eq fc7653a25de8
-- statement:
--   The P2 M Global Theory Zeta Local zeta  eq fc7653a25de8 construction uses the P2 M Global Theory Zeta Local zeta  eq fc7653a25de8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L9-L10

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

theorem P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8 {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by sorry

alias «GlobalTheory».«ZetaLocal».«zeta₁_eq» := P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8
