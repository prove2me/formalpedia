-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_algebraMap_mk_ne_zero_5503709ac0c7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_algebraMap_mk_ne_zero_5503709ac0c7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:19.976042+00:00
-- url     : https://prove2.me/theorems/51158de3-9d09-5af6-b85e-cac1ab98c9b0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim algebra Map mk ne zero 5503709ac0c7: P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim algebra Map mk ne zero 5503709ac0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim algebra Map mk ne zero 5503709ac0c7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Loc Dim algebra Map mk ne zero 5503709ac0c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartLocDim.lean#L39-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_algebraMap_mk_ne_zero_5503709ac0c7 (Q : Ideal (MRing ι F)) [Q.IsPrime] {g : MRing ι F} (hg : g ∉ Q) :
    algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q)) (Ideal.Quotient.mk Q g) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartLocDim».«algebraMap_mk_ne_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_algebraMap_mk_ne_zero_5503709ac0c7
