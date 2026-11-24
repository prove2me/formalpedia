-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521
-- name    : P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:01.485314+00:00
-- url     : https://prove2.me/theorems/13ddfda1-260b-4a4f-8a71-9739a3aff505
-- title:
--   P2 M Ground Theory Heights  Heights Height Rec R proof a841a96c8521: P2 M Ground Theory Heights  Heights Height Rec R proof a841a96c8521
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Rec R proof a841a96c8521 construction uses the P2 M Ground Theory Heights  Heights Height Rec R proof a841a96c8521 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PHeightRecR.lean#L50-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PHeightRecR.lean#L50-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitFiniteSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
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

theorem P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521 (hV : OrbitDivVertical.Statement) (hF : OrbitFiniteSum.Statement)
    (hA : OrbitArchSum.Statement) : HeightRecR.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightRecR».«proof» := P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521
