-- Prove2me | Theorems.Thm_P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b
-- name    : P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:47.238946+00:00
-- url     : https://prove2.me/theorems/f22ccbe9-d886-4659-8546-2c30886ecf37
-- title:
--   P2 M Global Theory Ka Unique Is Comb mul Vec  bb52f65ceb5b: P2 M Global Theory Ka Unique Is Comb mul Vec  bb52f65ceb5b
-- statement:
--   The P2 M Global Theory Ka Unique Is Comb mul Vec  bb52f65ceb5b construction uses the P2 M Global Theory Ka Unique Is Comb mul Vec  bb52f65ceb5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TopLeTranslate.lean#L204-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/TopLeTranslate.lean#L204-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) (L : LB X)
variable {π L}

theorem P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b {N N' : ℕ} {b : Fin N → ∀ i, Γ(X, L.U i)} {b' : Fin N' → ∀ i, Γ(X, L.U i)}
    {M : Matrix (Fin N) (Fin N') R} {f : ∀ i, Γ(X, L.U i)} {e : Fin N' → R}
    (hM : ∀ k, IsComb π L b (fun k' => M k' k) (b' k)) (he : IsComb π L b' e f) :
    IsComb π L b (M.mulVec e) f := by sorry

alias «GlobalTheory».«KaUnique».«IsComb».«mulVec'» := P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b
