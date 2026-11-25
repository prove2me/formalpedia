-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_nat_a2c113a363b2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_nat_a2c113a363b2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:44.900228+00:00
-- url     : https://prove2.me/theorems/6f8d3b3c-f3c8-435a-be1f-430569b274a3
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam snoc zpow nat a2c113a363b2: P2 M Ground Theory Heights  Heights Inter fam snoc zpow nat a2c113a363b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam snoc zpow nat a2c113a363b2 construction uses the P2 M Ground Theory Heights  Heights Inter fam snoc zpow nat a2c113a363b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L90-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L90-L105

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

theorem P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_nat_a2c113a363b2 (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X : HermLine ι} (hX : IsSmoothHerm X) (k : ℕ) :
    I P (n + 1) (Fin.snoc L (hermZpow X k)) = k * I P (n + 1) (Fin.snoc L X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«fam_snoc_zpow_nat» := P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_nat_a2c113a363b2
