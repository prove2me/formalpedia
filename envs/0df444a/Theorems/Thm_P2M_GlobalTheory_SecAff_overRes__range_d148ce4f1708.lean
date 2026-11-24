-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SecAff_overRes__range_d148ce4f1708
-- name    : P2M_GlobalTheory_SecAff_overRes__range_d148ce4f1708
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:15.995389+00:00
-- url     : https://prove2.me/theorems/3c6e7534-e69c-4eaf-95b5-b6d4b006f024
-- title:
--   P2 M Global Theory Sec Aff over Res  range d148ce4f1708: P2 M Global Theory Sec Aff over Res  range d148ce4f1708
-- statement:
--   The P2 M Global Theory Sec Aff over Res  range d148ce4f1708 construction uses the P2 M Global Theory Sec Aff over Res  range d148ce4f1708 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L505-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L505-L506

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}

theorem P2M_GlobalTheory_SecAff_overRes__range_d148ce4f1708 (V : T.left.Opens) : (overResι V).left.opensRange = V := by sorry

alias «GlobalTheory».«SecAff».«overResι_range» := P2M_GlobalTheory_SecAff_overRes__range_d148ce4f1708
