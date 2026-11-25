-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_anForm_maDens_eq_geo_maDensity_553a74f4fa53
-- name    : P2M_GroundTheory_Heights__Heights_anForm_maDens_eq_geo_maDensity_553a74f4fa53
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:34.747574+00:00
-- url     : https://prove2.me/theorems/4dbbfd97-ec87-5d0f-9d2a-debd38d243c5
-- title:
--   P2 M Ground Theory Heights  Heights an Form ma Dens eq geo ma Density 553a74f4fa53: P2 M Ground Theory Heights  Heights an Form ma Dens eq geo ma Density 553a74f4fa53
-- statement:
--   The P2 M Ground Theory Heights  Heights an Form ma Dens eq geo ma Density 553a74f4fa53 construction uses the P2 M Ground Theory Heights  Heights an Form ma Dens eq geo ma Density 553a74f4fa53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConePolar.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConePolar.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartGramMA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConePolar
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
open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_anForm_maDens_eq_geo_maDensity_553a74f4fa53 {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.ChartRestriction.G.Geo.maDensity φ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«anForm_maDens_eq_geo_maDensity» := P2M_GroundTheory_Heights__Heights_anForm_maDens_eq_geo_maDensity_553a74f4fa53
