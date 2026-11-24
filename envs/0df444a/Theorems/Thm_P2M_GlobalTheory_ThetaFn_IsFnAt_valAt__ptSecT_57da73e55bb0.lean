-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaFn_IsFnAt_valAt__ptSecT_57da73e55bb0
-- name    : P2M_GlobalTheory_ThetaFn_IsFnAt_valAt__ptSecT_57da73e55bb0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:38:43.239964+00:00
-- url     : https://prove2.me/theorems/04a1703d-5eeb-4b24-844b-f1344e954fbb
-- title:
--   P2 M Global Theory Theta Fn Is Fn At val At  pt Sec T 57da73e55bb0: P2 M Global Theory Theta Fn Is Fn At val At  pt Sec T 57da73e55bb0
-- statement:
--   The P2 M Global Theory Theta Fn Is Fn At val At  pt Sec T 57da73e55bb0 construction uses the P2 M Global Theory Theta Fn Is Fn At val At  pt Sec T 57da73e55bb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L481-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L481-L489

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

theorem P2M_GlobalTheory_ThetaFn_IsFnAt_valAt__ptSecT_57da73e55bb0 {k : ℤ} {s : LB.Sec (LPow A L k T)} {θ : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p k s θ) {x : T ⟶ A} {z : Fin g → ℂ} (hx : p ≫ x = u.ex z) (j : Fin 1 → L.ι)
    (hj : ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => x.left) j) :
    valAt' p.left (LB.wchart L (fun _ : Fin 1 => x.left) j)
      ((T.left.presheaf.map (homOfLE (val_le A L x j)).op).hom
        (((ptSecT A x).left.app _).hom (s.f j))) = θ z * u.fr (j 0) z ^ k := by sorry

alias «GlobalTheory».«ThetaFn».«IsFnAt».«valAt'_ptSecT» := P2M_GlobalTheory_ThetaFn_IsFnAt_valAt__ptSecT_57da73e55bb0
