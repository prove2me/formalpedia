-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_exists_isGoodProj_972436e4655c
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_exists_isGoodProj_972436e4655c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:37.158506+00:00
-- url     : https://prove2.me/theorems/4a3757f6-37aa-5669-8315-b370f8154851
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Points exists is Good Proj 972436e4655c: P2 M Ground Theory Heights  Heights Pts Integral Points exists is Good Proj 972436e4655c
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Points exists is Good Proj 972436e4655c construction uses the P2 M Ground Theory Heights  Heights Pts Integral Points exists is Good Proj 972436e4655c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L136-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
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
open ReciprocityTheory.ChartRestriction.G MeasureTheory
open GroundTheory.Heights₂.Heights.PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_exists_isGoodProj_972436e4655c (P : Ideal (Geo.MRing ι)) (hfin : Finite (projPts P)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), Geo.IsGoodProj P Ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralPoints».«exists_isGoodProj» := P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_exists_isGoodProj_972436e4655c
