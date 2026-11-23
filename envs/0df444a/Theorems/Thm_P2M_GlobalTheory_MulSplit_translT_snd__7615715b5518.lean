-- Prove2me | Theorems.Thm_P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518
-- name    : P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:43.727544+00:00
-- url     : https://prove2.me/theorems/97e089f3-35b9-4a1a-a300-8931c29e7549
-- title:
--   P2 M Global Theory Mul Split transl T snd  7615715b5518: P2 M Global Theory Mul Split transl T snd  7615715b5518
-- statement:
--   The P2 M Global Theory Mul Split transl T snd  7615715b5518 construction uses the P2 M Global Theory Mul Split transl T snd  7615715b5518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyEquivPiOfWeights.lean#L398-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyEquivPiOfWeights.lean#L398-L398

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

theorem P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518 (x : T ⟶ A) : translT A x ≫ snd T A = translPt A x := by sorry

alias «GlobalTheory».«MulSplit».«translT_snd'» := P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518
