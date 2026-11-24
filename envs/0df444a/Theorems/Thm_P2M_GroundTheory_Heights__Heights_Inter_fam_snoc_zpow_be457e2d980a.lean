-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_be457e2d980a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_be457e2d980a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:10.152879+00:00
-- url     : https://prove2.me/theorems/7df3a858-3337-4161-99b5-7f7c6c6e7009
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam snoc zpow be457e2d980a: P2 M Ground Theory Heights  Heights Inter fam snoc zpow be457e2d980a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam snoc zpow be457e2d980a construction uses the P2 M Ground Theory Heights  Heights Inter fam snoc zpow be457e2d980a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L107-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L107-L142

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

theorem P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_be457e2d980a (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (m : ℤ) :
    I P (n + 1) (Fin.snoc L (hermZpow X m)) = m * I P (n + 1) (Fin.snoc L X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«fam_snoc_zpow» := P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_be457e2d980a
