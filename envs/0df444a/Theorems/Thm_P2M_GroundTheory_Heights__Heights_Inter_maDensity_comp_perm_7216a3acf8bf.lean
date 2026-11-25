-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_maDensity_comp_perm_7216a3acf8bf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_maDensity_comp_perm_7216a3acf8bf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:23:07.784268+00:00
-- url     : https://prove2.me/theorems/bb795f36-a131-4a26-a32c-29e884ca8dda
-- title:
--   P2 M Ground Theory Heights  Heights Inter ma Density comp perm 7216a3acf8bf: P2 M Ground Theory Heights  Heights Inter ma Density comp perm 7216a3acf8bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ma Density comp perm 7216a3acf8bf construction uses the P2 M Ground Theory Heights  Heights Inter ma Density comp perm 7216a3acf8bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L24-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_maDensity_comp_perm_7216a3acf8bf (φ : Fin D → (Fin D → ℂ) → ℝ) (σ : Equiv.Perm (Fin D)) (z : Fin D → ℂ) :
    maDensity (φ ∘ σ) z = maDensity φ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«maDensity_comp_perm» := P2M_GroundTheory_Heights__Heights_Inter_maDensity_comp_perm_7216a3acf8bf
