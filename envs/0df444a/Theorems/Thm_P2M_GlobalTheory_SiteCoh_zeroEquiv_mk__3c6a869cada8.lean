-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SiteCoh_zeroEquiv_mk__3c6a869cada8
-- name    : P2M_GlobalTheory_SiteCoh_zeroEquiv_mk__3c6a869cada8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:47.791498+00:00
-- url     : https://prove2.me/theorems/2d2e3f36-410b-4586-a64b-82b92c1cfa13
-- title:
--   P2 M Global Theory Site Coh zero Equiv mk  3c6a869cada8: P2 M Global Theory Site Coh zero Equiv mk  3c6a869cada8
-- statement:
--   The P2 M Global Theory Site Coh zero Equiv mk  3c6a869cada8 construction uses the P2 M Global Theory Site Coh zero Equiv mk  3c6a869cada8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L109-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

theorem P2M_GlobalTheory_SiteCoh_zeroEquiv_mk__3c6a869cada8 (F : Sheaf J AddCommGrpCat.{v}) (U : C) (φ : (freeSheaf J).obj U ⟶ F) :
    zeroEquiv F U ((extEquiv F 0 U).symm (Ext.mk₀ φ)) = freeSheafHomEquiv U F φ := by sorry

alias «GlobalTheory».«SiteCoh».«zeroEquiv_mk₀» := P2M_GlobalTheory_SiteCoh_zeroEquiv_mk__3c6a869cada8
