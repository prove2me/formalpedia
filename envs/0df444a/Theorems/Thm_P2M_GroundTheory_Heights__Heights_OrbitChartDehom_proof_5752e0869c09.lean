-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartDehom_proof_5752e0869c09
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartDehom_proof_5752e0869c09
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:29.300847+00:00
-- url     : https://prove2.me/theorems/03c6063c-776a-5a97-90c0-9393645e0aec
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Dehom proof 5752e0869c09: P2 M Ground Theory Heights  Heights Orbit Chart Dehom proof 5752e0869c09
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Dehom proof 5752e0869c09 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Dehom proof 5752e0869c09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L133-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L133-L159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartDehom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3

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
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
variable {V}

theorem P2M_GroundTheory_Heights__Heights_OrbitChartDehom_proof_5752e0869c09 (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement) :
    OrbitChartDehom.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartDehom».«proof» := P2M_GroundTheory_Heights__Heights_OrbitChartDehom_proof_5752e0869c09
