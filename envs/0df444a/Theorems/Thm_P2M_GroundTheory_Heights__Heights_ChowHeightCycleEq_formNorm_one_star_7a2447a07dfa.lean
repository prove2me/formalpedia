-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:19.005254+00:00
-- url     : https://prove2.me/theorems/24808a0e-739c-41fb-9e7f-a675aa527a21
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq form Norm one star 7a2447a07dfa: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq form Norm one star 7a2447a07dfa
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq form Norm one star 7a2447a07dfa construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq form Norm one star 7a2447a07dfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L112-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa (u : Fin n → ℂ) :
    IndefiniteRowSideFullHecke.ArithBezout.formNorm (1 : Matrix (Fin n) (Fin n) ℂ) (star u) =
      IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«formNorm_one_star» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa
