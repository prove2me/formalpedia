-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_eq_famExt_551d8170ff5e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_fam_eq_famExt_551d8170ff5e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:25.561543+00:00
-- url     : https://prove2.me/theorems/5d2f8fb2-1e33-4776-88e6-ae8f2a0ed8aa
-- title:
--   P2 M Ground Theory Heights  Heights Inter fam eq fam Ext 551d8170ff5e: P2 M Ground Theory Heights  Heights Inter fam eq fam Ext 551d8170ff5e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fam eq fam Ext 551d8170ff5e construction uses the P2 M Ground Theory Heights  Heights Inter fam eq fam Ext 551d8170ff5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L184-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmAExpand.lean#L184-L241

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

theorem P2M_GroundTheory_Heights__Heights_Inter_fam_eq_famExt_551d8170ff5e (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) (T : Finset (Fin (n + 1))) (t : Fin (n + 1) → Fin 2) :
    I P (n + 1) (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) =
      famExt I P (n + 1) ![X, A] (fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (t j) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«fam_eq_famExt» := P2M_GroundTheory_Heights__Heights_Inter_fam_eq_famExt_551d8170ff5e
