-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitLocalSum_proof_7d04b33757f3
-- name    : P2M_GroundTheory_Heights__Heights_OrbitLocalSum_proof_7d04b33757f3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:46.95789+00:00
-- url     : https://prove2.me/theorems/e8587ecc-ad1a-48e3-b989-df652bbb9b8b
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Local Sum proof 7d04b33757f3: P2 M Ground Theory Heights  Heights Orbit Local Sum proof 7d04b33757f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Local Sum proof 7d04b33757f3 construction uses the P2 M Ground Theory Heights  Heights Orbit Local Sum proof 7d04b33757f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitLocalSum.lean#L17-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitLocalSum.lean#L17-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitLocalSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalLengthPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitLocalSum
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem P2M_GroundTheory_Heights__Heights_OrbitLocalSum_proof_7d04b33757f3 (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitLocalSum».«proof» := P2M_GroundTheory_Heights__Heights_OrbitLocalSum_proof_7d04b33757f3
