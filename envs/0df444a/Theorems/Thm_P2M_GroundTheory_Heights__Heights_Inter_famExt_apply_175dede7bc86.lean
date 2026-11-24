-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_apply_175dede7bc86
-- name    : P2M_GroundTheory_Heights__Heights_Inter_famExt_apply_175dede7bc86
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:23.344861+00:00
-- url     : https://prove2.me/theorems/fdac0593-1a8c-4c3f-b62f-41fa5b174eb6
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam Ext apply 175dede7bc86: P2 M Ground Theory Heights  Heights Inter fam Ext apply 175dede7bc86
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam Ext apply 175dede7bc86 construction uses the P2 M Ground Theory Heights  Heights Inter fam Ext apply 175dede7bc86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L51-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_famExt_apply_175dede7bc86 (e : Fin 2 → HermLine ι) (v : Fin n → Fin 2 → ℝ) :
    famExt I P n e v = ∑ s : Fin n → Fin 2, I P n (e ∘ s) * ∏ j, v j (s j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«famExt_apply» := P2M_GroundTheory_Heights__Heights_Inter_famExt_apply_175dede7bc86
