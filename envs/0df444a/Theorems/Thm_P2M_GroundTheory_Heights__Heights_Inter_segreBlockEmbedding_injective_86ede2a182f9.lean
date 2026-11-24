-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_segreBlockEmbedding_injective_86ede2a182f9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_segreBlockEmbedding_injective_86ede2a182f9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:16.247244+00:00
-- url     : https://prove2.me/theorems/e79af873-8f3b-4291-b6f6-4a07e134b77a
-- title:
--   P2 M Ground Theory Heights  Heights Inter segre Block Embedding injective 86ede2a182f9: P2 M Ground Theory Heights  Heights Inter segre Block Embedding injective 86ede2a182f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter segre Block Embedding injective 86ede2a182f9 construction uses the P2 M Ground Theory Heights  Heights Inter segre Block Embedding injective 86ede2a182f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L764-L766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L764-L766

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

theorem P2M_GroundTheory_Heights__Heights_Inter_segreBlockEmbedding_injective_86ede2a182f9 (j : Fin 2) : Function.Injective (diagonalBlockIndex j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«segreBlockEmbedding_injective» := P2M_GroundTheory_Heights__Heights_Inter_segreBlockEmbedding_injective_86ede2a182f9
