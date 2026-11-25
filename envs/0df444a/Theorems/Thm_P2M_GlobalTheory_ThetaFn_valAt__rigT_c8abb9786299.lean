-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299
-- name    : P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:38:14.628863+00:00
-- url     : https://prove2.me/theorems/c43f0d13-02ed-4029-a477-32cba985e2a7
-- title:
--   P2 M Global Theory Theta Fn val At  rig T c8abb9786299: P2 M Global Theory Theta Fn val At  rig T c8abb9786299
-- statement:
--   The P2 M Global Theory Theta Fn val At  rig T c8abb9786299 construction uses the P2 M Global Theory Theta Fn val At  rig T c8abb9786299 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L522-L534
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L522-L534

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
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)
variable {u p}
variable (p)

theorem P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299 {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig) (k : ℤ)
    (j : Fin 1 → L.ι) (hj : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U (j 0)) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j)
      ((rigT A L rig T k).s j).val = u.fr (j 0) 0 ^ k := by sorry

alias «GlobalTheory».«ThetaFn».«valAt'_rigT» := P2M_GlobalTheory_ThetaFn_valAt__rigT_c8abb9786299
