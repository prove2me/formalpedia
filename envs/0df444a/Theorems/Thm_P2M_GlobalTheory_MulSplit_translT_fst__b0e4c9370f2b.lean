-- Prove2me | Theorems.Thm_P2M_GlobalTheory_MulSplit_translT_fst__b0e4c9370f2b
-- name    : P2M_GlobalTheory_MulSplit_translT_fst__b0e4c9370f2b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:37.528492+00:00
-- url     : https://prove2.me/theorems/30b74078-f9da-4504-ac50-00d99f23d903
-- title:
--   P2 M Global Theory Mul Split transl T fst  b0e4c9370f2b: P2 M Global Theory Mul Split transl T fst  b0e4c9370f2b
-- statement:
--   The P2 M Global Theory Mul Split transl T fst  b0e4c9370f2b construction uses the P2 M Global Theory Mul Split transl T fst  b0e4c9370f2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyEquivPiOfWeights.lean#L396-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyEquivPiOfWeights.lean#L396-L396

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

theorem P2M_GlobalTheory_MulSplit_translT_fst__b0e4c9370f2b (x : T ⟶ A) : translT A x ≫ fst T A = fst T A := by sorry

alias «GlobalTheory».«MulSplit».«translT_fst'» := P2M_GlobalTheory_MulSplit_translT_fst__b0e4c9370f2b
