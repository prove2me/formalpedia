-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SiteCoh_equiv__terminalEquiv_79b4d00cc8cf
-- name    : P2M_GlobalTheory_SiteCoh_equiv__terminalEquiv_79b4d00cc8cf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:56.437372+00:00
-- url     : https://prove2.me/theorems/5abe2175-b663-41c1-80ff-da7aa2afe136
-- title:
--   P2 M Global Theory Site Coh equiv  terminal Equiv 79b4d00cc8cf: P2 M Global Theory Site Coh equiv  terminal Equiv 79b4d00cc8cf
-- statement:
--   The P2 M Global Theory Site Coh equiv  terminal Equiv 79b4d00cc8cf construction uses the P2 M Global Theory Site Coh equiv  terminal Equiv 79b4d00cc8cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L151-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L151-L165

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

theorem P2M_GlobalTheory_SiteCoh_equiv__terminalEquiv_79b4d00cc8cf (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T)
    (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (terminalEquiv F 0 hT x) = zeroEquiv F T x := by sorry

alias «GlobalTheory».«SiteCoh».«equiv₀_terminalEquiv» := P2M_GlobalTheory_SiteCoh_equiv__terminalEquiv_79b4d00cc8cf
