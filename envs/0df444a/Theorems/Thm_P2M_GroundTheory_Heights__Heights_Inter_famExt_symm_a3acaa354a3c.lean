-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_symm_a3acaa354a3c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_famExt_symm_a3acaa354a3c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:48.863805+00:00
-- url     : https://prove2.me/theorems/52485e36-154d-4993-b122-c561bff22bf6
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam Ext symm a3acaa354a3c: P2 M Ground Theory Heights  Heights Inter fam Ext symm a3acaa354a3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam Ext symm a3acaa354a3c construction uses the P2 M Ground Theory Heights  Heights Inter fam Ext symm a3acaa354a3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L70-L79

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

theorem P2M_GroundTheory_Heights__Heights_Inter_famExt_symm_a3acaa354a3c (hI : IsIntersectionFamily I) (hP : IsArithVar P n) (e : Fin 2 → HermLine ι)
    (he : ∀ i, IsSmoothHerm (e i)) : IsSymmForm (famExt I P n e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«famExt_symm» := P2M_GroundTheory_Heights__Heights_Inter_famExt_symm_a3acaa354a3c
