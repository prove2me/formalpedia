-- Prove2me | Theorems.Thm_P2M_GlobalTheory_algebra_OfHom_algebraMap_6568cc1e9975
-- name    : P2M_GlobalTheory_algebra_OfHom_algebraMap_6568cc1e9975
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:44.585905+00:00
-- url     : https://prove2.me/theorems/8b49e7aa-c1ec-4bca-a26f-6d01116e08c8
-- title:
--   P2 M Global Theory algebra Of Hom algebra Map 6568cc1e9975: P2 M Global Theory algebra Of Hom algebra Map 6568cc1e9975
-- statement:
--   The P2 M Global Theory algebra Of Hom algebra Map 6568cc1e9975 construction uses the P2 M Global Theory algebra Of Hom algebra Map 6568cc1e9975 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L554-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L554-L556

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}

theorem P2M_GlobalTheory_algebra_OfHom_algebraMap_6568cc1e9975 {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (r : R) :
    letI := algebraΓOfHom f
    algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := by sorry

alias «GlobalTheory».«algebraΓOfHom_algebraMap» := P2M_GlobalTheory_algebra_OfHom_algebraMap_6568cc1e9975
