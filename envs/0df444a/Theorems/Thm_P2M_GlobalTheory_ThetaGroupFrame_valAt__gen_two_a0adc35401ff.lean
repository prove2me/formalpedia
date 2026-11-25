-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_two_a0adc35401ff
-- name    : P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_two_a0adc35401ff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:01.127416+00:00
-- url     : https://prove2.me/theorems/faa095de-7092-482b-bc68-c0c67a0af476
-- title:
--   P2 M Global Theory Theta Group Frame val At  gen two a0adc35401ff: P2 M Global Theory Theta Group Frame val At  gen two a0adc35401ff
-- statement:
--   The P2 M Global Theory Theta Group Frame val At  gen two a0adc35401ff construction uses the P2 M Global Theory Theta Group Frame val At  gen two a0adc35401ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L98-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L98-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame

theorem P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_two_a0adc35401ff (hv : ValLaws) {X Y : Scheme.{0}} (L : LB X) (φ₀ φ₁ : Y ⟶ X) (k : ℕ)
    (c : LB.Gen (LB.LinComb L (K := Fin 2) ![φ₀, φ₁] ![(k : ℤ), -(k : ℤ)])) (hc : c.IsGen)
    (x : Sp ℂ ⟶ Y) (y₀ y₁ : Sp ℂ ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁)
    (j j' : Fin 2 → L.ι) (a₀ : ⊤ ≤ y₀ ⁻¹ᵁ L.U (j 0)) (a₁ : ⊤ ≤ y₁ ⁻¹ᵁ L.U (j 1))
    (b₀ : ⊤ ≤ y₀ ⁻¹ᵁ L.U (j' 0)) (b₁ : ⊤ ≤ y₁ ⁻¹ᵁ L.U (j' 1)) :
    valAt' x (LB.wchart L ![φ₀, φ₁] j) (c.s j).val =
      valAt' y₀ (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val ^ k *
        (valAt' y₁ (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val ^ k)⁻¹ *
        valAt' x (LB.wchart L ![φ₀, φ₁] j') (c.s j').val := by sorry

alias «GlobalTheory».«ThetaGroupFrame».«valAt'_gen_two» := P2M_GlobalTheory_ThetaGroupFrame_valAt__gen_two_a0adc35401ff
