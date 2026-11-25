-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ex_isPull0_9061b183e0fe
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ex_isPull0_9061b183e0fe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:43.540403+00:00
-- url     : https://prove2.me/theorems/dd5e2956-8134-4887-94ed-1f61a0be1978
-- title:
--   P2 M Ground Theory Heights  Heights Inter ex is Pull0 9061b183e0fe: P2 M Ground Theory Heights  Heights Inter ex is Pull0 9061b183e0fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ex is Pull0 9061b183e0fe construction uses the P2 M Ground Theory Heights  Heights Inter ex is Pull0 9061b183e0fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L780-L789
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L780-L789

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ex_isPull0_9061b183e0fe (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) (HermLine.ofMetrics (fun k => fsMetric (ExY k)) c) (exPull 0 c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ex_isPull0» := P2M_GroundTheory_Heights__Heights_Inter_ex_isPull0_9061b183e0fe
