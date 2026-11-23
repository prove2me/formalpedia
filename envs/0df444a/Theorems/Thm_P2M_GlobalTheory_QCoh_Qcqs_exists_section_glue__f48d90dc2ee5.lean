-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5
-- name    : P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:37.392327+00:00
-- url     : https://prove2.me/theorems/ad8148b0-b99b-425e-964a-e78f4cf9e883
-- title:
--   P2 M Global Theory QCoh Qcqs exists section glue  f48d90dc2ee5: P2 M Global Theory QCoh Qcqs exists section glue  f48d90dc2ee5
-- statement:
--   The P2 M Global Theory QCoh Qcqs exists section glue  f48d90dc2ee5 construction uses the P2 M Global Theory QCoh Qcqs exists section glue  f48d90dc2ee5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L111-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L111-L129

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

theorem P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5 (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s₁ : Γ(F, V₁))
    (s₂ : Γ(F, V₂))
    (e : F.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      F.presheaf.map (homOfLE inf_le_right).op s₂) :
    ∃ s : Γ(F, W), F.presheaf.map (homOfLE h₁).op s = s₁ ∧
      F.presheaf.map (homOfLE h₂).op s = s₂ := by sorry

alias «GlobalTheory».«QCoh».«Qcqs».«exists_section_glue₂» := P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5
