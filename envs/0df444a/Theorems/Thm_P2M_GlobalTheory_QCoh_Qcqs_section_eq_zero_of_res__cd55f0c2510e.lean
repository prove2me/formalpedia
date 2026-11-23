-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
-- name    : P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:09.57572+00:00
-- url     : https://prove2.me/theorems/4cc4f405-6991-4230-82cc-e830a7a0e91d
-- title:
--   P2 M Global Theory QCoh Qcqs section eq zero of res  cd55f0c2510e: P2 M Global Theory QCoh Qcqs section eq zero of res  cd55f0c2510e
-- statement:
--   The P2 M Global Theory QCoh Qcqs section eq zero of res  cd55f0c2510e construction uses the P2 M Global Theory QCoh Qcqs section eq zero of res  cd55f0c2510e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L105-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}

theorem P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s : Γ(F, W))
    (e₁ : F.presheaf.map (homOfLE h₁).op s = 0) (e₂ : F.presheaf.map (homOfLE h₂).op s = 0) :
    s = 0 := by sorry

alias «GlobalTheory».«QCoh».«Qcqs».«section_eq_zero_of_res₂» := P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
