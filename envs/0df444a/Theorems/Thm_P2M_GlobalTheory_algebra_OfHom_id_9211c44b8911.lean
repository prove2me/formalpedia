-- Prove2me | Theorems.Thm_P2M_GlobalTheory_algebra_OfHom_id_9211c44b8911
-- name    : P2M_GlobalTheory_algebra_OfHom_id_9211c44b8911
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:40.235053+00:00
-- url     : https://prove2.me/theorems/ec4673f5-b2ce-5662-8232-d3bbfd466390
-- title:
--   P2 M Global Theory algebra Of Hom id 9211c44b8911: P2 M Global Theory algebra Of Hom id 9211c44b8911
-- statement:
--   The P2 M Global Theory algebra Of Hom id 9211c44b8911 construction uses the P2 M Global Theory algebra Of Hom id 9211c44b8911 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L560-L562
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L560-L562

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

theorem P2M_GlobalTheory_algebra_OfHom_id_9211c44b8911 (R : Type u) [CommRing R] :
    algebraΓOfHom (𝟙 (Spec (.of R))) = algebraΓSpec (.of R) := by sorry

alias «GlobalTheory».«algebraΓOfHom_id» := P2M_GlobalTheory_algebra_OfHom_id_9211c44b8911
