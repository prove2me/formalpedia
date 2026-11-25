-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WeightGen_HasGen_iso__e42ac449ccba
-- name    : P2M_GlobalTheory_WeightGen_HasGen_iso__e42ac449ccba
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:41.48515+00:00
-- url     : https://prove2.me/theorems/9a743541-b4df-426b-bb9b-058849dac4aa
-- title:
--   P2 M Global Theory Weight Gen Has Gen iso  e42ac449ccba: P2 M Global Theory Weight Gen Has Gen iso  e42ac449ccba
-- statement:
--   The P2 M Global Theory Weight Gen Has Gen iso  e42ac449ccba construction uses the P2 M Global Theory Weight Gen Has Gen iso  e42ac449ccba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L131-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyGtCoordOfIsGt.lean#L131-L147

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}

theorem P2M_GlobalTheory_WeightGen_HasGen_iso__e42ac449ccba (h : a ≫ q = p ≫ q) {L M : LB B} {c : GermFn P} (hM : HasGen q a p M c)
    (cov : ∀ x, ∃ k, x ∈ M.U k) (w : LB.Iso L M) (hw : w.IsGen) : HasGen q a p L c := by sorry

alias «GlobalTheory».«WeightGen».«HasGen».«iso'» := P2M_GlobalTheory_WeightGen_HasGen_iso__e42ac449ccba
