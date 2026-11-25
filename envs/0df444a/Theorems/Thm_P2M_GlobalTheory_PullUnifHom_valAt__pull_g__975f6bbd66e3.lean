-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PullUnifHom_valAt__pull_g__975f6bbd66e3
-- name    : P2M_GlobalTheory_PullUnifHom_valAt__pull_g__975f6bbd66e3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:44.297245+00:00
-- url     : https://prove2.me/theorems/f13b9c21-1831-429f-92a5-da81b0c50555
-- title:
--   P2 M Global Theory Pull Unif Hom val At  pull g  975f6bbd66e3: P2 M Global Theory Pull Unif Hom val At  pull g  975f6bbd66e3
-- statement:
--   The P2 M Global Theory Pull Unif Hom val At  pull g  975f6bbd66e3 construction uses the P2 M Global Theory Pull Unif Hom val At  pull g  975f6bbd66e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHolUnifPullAlongGroupHom.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHolUnifPullAlongGroupHom.lean#L32-L41

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

theorem P2M_GlobalTheory_PullUnifHom_valAt__pull_g__975f6bbd66e3 (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by sorry

alias «GlobalTheory».«PullUnifHom».«valAt'_pull_g'» := P2M_GlobalTheory_PullUnifHom_valAt__pull_g__975f6bbd66e3
