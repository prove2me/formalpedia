-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_toH__smul_89e6e45ccfe4
-- name    : P2M_GlobalTheory_cohOn_toH__smul_89e6e45ccfe4
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:40.171226+00:00
-- url     : https://prove2.me/theorems/781e8787-0965-4a62-8066-ca1d1321daba
-- title:
--   P2 M Global Theory coh On to H  smul 89e6e45ccfe4: P2 M Global Theory coh On to H  smul 89e6e45ccfe4
-- statement:
--   The P2 M Global Theory coh On to H  smul 89e6e45ccfe4 construction uses the P2 M Global Theory coh On to H  smul 89e6e45ccfe4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L64-L67

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
variable {R}

theorem P2M_GlobalTheory_cohOn_toH__smul_89e6e45ccfe4 {F : X.Modules} {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    toH' F U n (r • x) =
      SiteCoh.map ((toAbSheaf X).map (smulHom F (algebraMap R Γ(X, ⊤) r))) n U (toH' F U n x) := by sorry

alias «GlobalTheory».«cohOn».«toH'_smul» := P2M_GlobalTheory_cohOn_toH__smul_89e6e45ccfe4
