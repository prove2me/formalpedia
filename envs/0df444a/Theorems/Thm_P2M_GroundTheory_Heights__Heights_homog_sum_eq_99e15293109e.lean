-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e
-- name    : P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:18.027821+00:00
-- url     : https://prove2.me/theorems/3e905d6a-a9a3-4090-9ec7-ad9123ebfdb1
-- title:
--   P2 M Ground Theory Heights  Heights homog sum eq 99e15293109e: P2 M Ground Theory Heights  Heights homog sum eq 99e15293109e
-- statement:
--   The P2 M Ground Theory Heights  Heights homog sum eq 99e15293109e construction uses the P2 M Ground Theory Heights  Heights homog sum eq 99e15293109e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L21-L30

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

theorem P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e {F : Type*} [Field F] (g : Polynomial ℤ) (u v : F) (hv : v ≠ 0) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * v ^ (g.natDegree - j) =
      v ^ g.natDegree * Polynomial.aeval (u / v) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«homog_sum_eq» := P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e
