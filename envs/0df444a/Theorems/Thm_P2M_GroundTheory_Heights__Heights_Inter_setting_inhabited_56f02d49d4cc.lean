-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_setting_inhabited_56f02d49d4cc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_setting_inhabited_56f02d49d4cc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:17.773265+00:00
-- url     : https://prove2.me/theorems/d52d27cc-67b3-44fd-8583-63da1cabea69
-- title:
--   P2 M Ground Theory Heights  Heights Inter setting inhabited 56f02d49d4cc: P2 M Ground Theory Heights  Heights Inter setting inhabited 56f02d49d4cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter setting inhabited 56f02d49d4cc construction uses the P2 M Ground Theory Heights  Heights Inter setting inhabited 56f02d49d4cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L802-L810
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L802-L810

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ

theorem P2M_GroundTheory_Heights__Heights_Inter_setting_inhabited_56f02d49d4cc :
    ∃ (S : ProjectiveLineBundle 1) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
      S.IsXi X ∧ IsSmoothHerm A ∧ IsFromBase A ∧
      IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ ∧ IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ ∧
      IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ ∧
      IsSmoothHerm X₀ ∧ IsSmoothHerm X₁ ∧ IsSmoothHerm A₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«setting_inhabited» := P2M_GroundTheory_Heights__Heights_Inter_setting_inhabited_56f02d49d4cc
