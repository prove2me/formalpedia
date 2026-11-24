-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986
-- name    : P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:36.249541+00:00
-- url     : https://prove2.me/theorems/59f6c65a-aa5b-486b-bb82-95dd24576874
-- title:
--   P2 M Ground Theory Heights  Heights Dual Arithmetic Variety is Algebraic of adjoin b50a6ba2f986: P2 M Ground Theory Heights  Heights Dual Arithmetic Variety is Algebraic of adjoin b50a6ba2f986
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Arithmetic Variety is Algebraic of adjoin b50a6ba2f986 construction uses the P2 M Ground Theory Heights  Heights Dual Arithmetic Variety is Algebraic of adjoin b50a6ba2f986 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualArithVar.lean#L46-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]

theorem P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986 {m : ℕ} (S : Set (ProjField K m))
    (h : ∀ z, z ∈ IntermediateField.adjoin K S) :
    Algebra.IsAlgebraic (Algebra.adjoin K S) (ProjField K m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualArithmeticVariety».«isAlgebraic_of_adjoin» := P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_isAlgebraic_of_adjoin_b50a6ba2f986
