-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneMapQ_chartHomogQ_93cff86ca181
-- name    : P2M_GroundTheory_Heights__Heights_coneMapQ_chartHomogQ_93cff86ca181
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:33.370798+00:00
-- url     : https://prove2.me/theorems/bf90a10e-c778-4a34-b683-39acbb39054d
-- title:
--   P2 M Ground Theory Heights  Heights cone Map Q chart Homog Q 93cff86ca181: P2 M Ground Theory Heights  Heights cone Map Q chart Homog Q 93cff86ca181
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Map Q chart Homog Q 93cff86ca181 construction uses the P2 M Ground Theory Heights  Heights cone Map Q chart Homog Q 93cff86ca181 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatioLemmas.lean#L47-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_coneMapQ_chartHomogQ_93cff86ca181 (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    OrbitCurve.coneMapQ x (chartHomogQ c f) =
      C (aeval (flatCone x) (chartHomogQ c f)) * ∏ p : Coord n, X p.1 ^ f.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneMapQ_chartHomogQ» := P2M_GroundTheory_Heights__Heights_coneMapQ_chartHomogQ_93cff86ca181
