-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_of_isPullHerm__2060c364192b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_of_isPullHerm__2060c364192b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:14.815338+00:00
-- url     : https://prove2.me/theorems/eda76314-8fe4-51d6-a900-cd6879f4948f
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Smooth Herm of is Pull Herm  2060c364192b: P2 M Ground Theory Heights  Heights Inter is Smooth Herm of is Pull Herm  2060c364192b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Smooth Herm of is Pull Herm  2060c364192b construction uses the P2 M Ground Theory Heights  Heights Inter is Smooth Herm of is Pull Herm  2060c364192b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFStep.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFStep.lean#L21-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFStep
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_of_isPullHerm__2060c364192b {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isSmoothHerm_of_isPullHerm'» := P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_of_isPullHerm__2060c364192b
