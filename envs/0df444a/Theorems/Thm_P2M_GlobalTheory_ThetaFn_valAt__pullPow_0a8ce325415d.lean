-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__pullPow_0a8ce325415d
-- name    : P2M_GlobalTheory_ThetaFn_valAt__pullPow_0a8ce325415d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:57.698393+00:00
-- url     : https://prove2.me/theorems/ece65b4d-daf3-406e-9f62-e1b0906c2e92
-- title:
--   P2 M Global Theory Theta Fn val At  pull Pow 0a8ce325415d: P2 M Global Theory Theta Fn val At  pull Pow 0a8ce325415d
-- statement:
--   The P2 M Global Theory Theta Fn val At  pull Pow 0a8ce325415d construction uses the P2 M Global Theory Theta Fn val At  pull Pow 0a8ce325415d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L154-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] [Unique K]
  [Unique K']

theorem P2M_GlobalTheory_ThetaFn_valAt__pullPow_0a8ce325415d {φ : Y ⟶ X} {ψ : Z ⟶ X} (h : Z ⟶ Y) (e : h ≫ φ = ψ) (a : ℤ)
    (s : LB.Sec (LB.LinComb L (fun _ : K => φ) (fun _ => a))) (x : Sp ℂ ⟶ Z) (j : K' → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K' => ψ) j) :
    valAt' x (LB.wchart L (fun _ : K' => ψ) j) ((pullPow L (K' := K') h e a s).f j) =
      valAt' (x ≫ h) (LB.wchart L (fun _ : K => φ) (fun _ => j default))
        (s.f (fun _ => j default)) := by sorry

alias «GlobalTheory».«ThetaFn».«valAt'_pullPow» := P2M_GlobalTheory_ThetaFn_valAt__pullPow_0a8ce325415d
