-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774
-- name    : P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:15.088535+00:00
-- url     : https://prove2.me/theorems/42934a32-ffac-403b-bef0-29c1c0f4f808
-- title:
--   P2 M Ground Theory Heights  Heights homog sum zero e8577340b774: P2 M Ground Theory Heights  Heights homog sum zero e8577340b774
-- statement:
--   The P2 M Ground Theory Heights  Heights homog sum zero e8577340b774 construction uses the P2 M Ground Theory Heights  Heights homog sum zero e8577340b774 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L32-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
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

theorem P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774 {F : Type*} [CommRing F] (g : Polynomial ℤ) (u : F) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * (0 : F) ^ (g.natDegree - j) =
      (g.leadingCoeff : F) * u ^ g.natDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«homog_sum_zero» := P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774
