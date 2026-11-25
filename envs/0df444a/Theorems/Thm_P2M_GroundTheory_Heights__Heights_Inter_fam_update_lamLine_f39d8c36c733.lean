-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_update_lamLine_f39d8c36c733
-- name    : P2M_GroundTheory_Heights__Heights_Inter_fam_update_lamLine_f39d8c36c733
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:17.461654+00:00
-- url     : https://prove2.me/theorems/927ab323-5e9e-4d18-809d-15d2be5e4c8d
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam update lam Line f39d8c36c733: P2 M Ground Theory Heights  Heights Inter fam update lam Line f39d8c36c733
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam update lam Line f39d8c36c733 construction uses the P2 M Ground Theory Heights  Heights Inter fam update lam Line f39d8c36c733 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L165-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L165-L182

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

theorem P2M_GroundTheory_Heights__Heights_Inter_fam_update_lamLine_f39d8c36c733 (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) :
    I P (n + 1) (Function.update L a (lamLine A X c)) =
      2 * I P (n + 1) (Function.update L a A) - c * I P (n + 1) (Function.update L a X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«fam_update_lamLine» := P2M_GroundTheory_Heights__Heights_Inter_fam_update_lamLine_f39d8c36c733
