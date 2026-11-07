-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_originalRow_injective
-- name    : QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.originalRow_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:39:17.663687+00:00
-- url     : https://prove2.me/theorems/7b11709c-115c-4f1f-a574-0b9fabc278f1
-- title:
--   Classical Row Reduction: original Row injective
-- statement:
--   The Classical Row Reduction construction uses the original Row injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L214-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L214-L219

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20 QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]

theorem QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.originalRow_injective
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Function.Injective (originalRow Y) := by sorry
