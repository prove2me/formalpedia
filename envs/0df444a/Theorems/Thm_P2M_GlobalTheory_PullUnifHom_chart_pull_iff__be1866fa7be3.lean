-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PullUnifHom_chart_pull_iff__be1866fa7be3
-- name    : P2M_GlobalTheory_PullUnifHom_chart_pull_iff__be1866fa7be3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:43.942906+00:00
-- url     : https://prove2.me/theorems/c5b4ddab-1c1b-4cf8-8eb2-6218f8bdf821
-- title:
--   P2 M Global Theory Pull Unif Hom chart pull iff  be1866fa7be3: P2 M Global Theory Pull Unif Hom chart pull iff  be1866fa7be3
-- statement:
--   The P2 M Global Theory Pull Unif Hom chart pull iff  be1866fa7be3 construction uses the P2 M Global Theory Pull Unif Hom chart pull iff  be1866fa7be3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHolUnifPullAlongGroupHom.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHolUnifPullAlongGroupHom.lean#L22-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHolUnifPullAlongGroupHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.PullUnifHom
open GlobalTheory.PullHermitian
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_PullUnifHom_chart_pull_iff__be1866fa7be3 (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) := by sorry

alias «GlobalTheory».«PullUnifHom».«chart_pull_iff'» := P2M_GlobalTheory_PullUnifHom_chart_pull_iff__be1866fa7be3
