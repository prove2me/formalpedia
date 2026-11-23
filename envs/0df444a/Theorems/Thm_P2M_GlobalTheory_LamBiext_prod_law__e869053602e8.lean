-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LamBiext_prod_law__e869053602e8
-- name    : P2M_GlobalTheory_LamBiext_prod_law__e869053602e8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:42:24.168592+00:00
-- url     : https://prove2.me/theorems/59fd8c40-f5b9-4e07-9b87-679087e48e0e
-- title:
--   P2 M Global Theory Lam Biext prod law  e869053602e8: P2 M Global Theory Lam Biext prod law  e869053602e8
-- statement:
--   The P2 M Global Theory Lam Biext prod law  e869053602e8 construction uses the P2 M Global Theory Lam Biext prod law  e869053602e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L114-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLaws.lean#L114-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem P2M_GlobalTheory_LamBiext_prod_law__e869053602e8 {T : Over S} (a b c : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 G).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (a * b) c).left * (h (lift a c).left)⁻¹ * (h (lift b c).left)⁻¹ := by sorry

alias «GlobalTheory».«LamBiext».«prod_law₁» := P2M_GlobalTheory_LamBiext_prod_law__e869053602e8
