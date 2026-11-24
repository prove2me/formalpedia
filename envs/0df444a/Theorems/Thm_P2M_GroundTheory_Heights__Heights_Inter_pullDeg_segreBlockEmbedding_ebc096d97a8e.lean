-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:54.341317+00:00
-- url     : https://prove2.me/theorems/68a81591-3d98-4a8c-9822-4b168c4a357c
-- title:
--   P2 M Ground Theory Heights  Heights Inter pull Deg segre Block Embedding ebc096d97a8e: P2 M Ground Theory Heights  Heights Inter pull Deg segre Block Embedding ebc096d97a8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter pull Deg segre Block Embedding ebc096d97a8e construction uses the P2 M Ground Theory Heights  Heights Inter pull Deg segre Block Embedding ebc096d97a8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L768-L770
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L768-L770

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e (j : Fin 2) (c : T.YBlk → ℤ) (k : T.YBlk) :
    I1.pullDeg (diagonalBlockIndex j) c (diagonalBlockIndex j k) = c k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pullDeg_segreBlockEmbedding» := P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e
