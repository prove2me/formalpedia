-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_lamLine_expand_e4a84c081deb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_fam_lamLine_expand_e4a84c081deb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:39.119925+00:00
-- url     : https://prove2.me/theorems/0ed07def-60dc-43ba-a96f-6824880688f8
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam lam Line expand e4a84c081deb: P2 M Ground Theory Heights  Heights Inter fam lam Line expand e4a84c081deb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam lam Line expand e4a84c081deb construction uses the P2 M Ground Theory Heights  Heights Inter fam lam Line expand e4a84c081deb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L243-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L243-L273

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

theorem P2M_GroundTheory_Heights__Heights_Inter_fam_lamLine_expand_e4a84c081deb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) :
    I P (n + 1) (fun _ => lamLine A X c) =
      2 ^ (n + 1) * ∑ j ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose j : ℝ) * (-(c : ℝ) / 2) ^ j * I P (n + 1) (mix j X A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«fam_lamLine_expand» := P2M_GroundTheory_Heights__Heights_Inter_fam_lamLine_expand_e4a84c081deb
