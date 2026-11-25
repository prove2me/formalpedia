-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_to__zeroEquiv_e3a9394c2519
-- name    : P2M_GlobalTheory_cohOn_to__zeroEquiv_e3a9394c2519
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:57.63075+00:00
-- url     : https://prove2.me/theorems/d9f261d6-0eb5-466f-9e85-55a5b786ead5
-- title:
--   P2 M Global Theory coh On to  zero Equiv e3a9394c2519: P2 M Global Theory coh On to  zero Equiv e3a9394c2519
-- statement:
--   The P2 M Global Theory coh On to  zero Equiv e3a9394c2519 construction uses the P2 M Global Theory coh On to  zero Equiv e3a9394c2519 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L438-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L438-L440

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
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G : X.Modules} {U V : X.Opens}

theorem P2M_GlobalTheory_cohOn_to__zeroEquiv_e3a9394c2519 (x : cohOn F U 0) :
    sectionsOn.toΓ F U (zeroEquiv R F U x) =
      SiteCoh.zeroEquiv ((toAbSheaf X).obj F) U (toH' F U 0 x) := by sorry

alias «GlobalTheory».«cohOn».«toΓ_zeroEquiv» := P2M_GlobalTheory_cohOn_to__zeroEquiv_e3a9394c2519
