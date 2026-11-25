-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QCoh_nonempty_presentation_restrict___3b59af861bdd
-- name    : P2M_GlobalTheory_QCoh_nonempty_presentation_restrict___3b59af861bdd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:53.382795+00:00
-- url     : https://prove2.me/theorems/7beb0524-c4c2-496b-981b-eea2a511f99f
-- title:
--   P2 M Global Theory QCoh nonempty presentation restrict   3b59af861bdd: P2 M Global Theory QCoh nonempty presentation restrict   3b59af861bdd
-- statement:
--   The P2 M Global Theory QCoh nonempty presentation restrict   3b59af861bdd construction uses the P2 M Global Theory QCoh nonempty presentation restrict   3b59af861bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L206-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L206-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
set_option backward.isDefEq.respectTransparency false

theorem P2M_GlobalTheory_QCoh_nonempty_presentation_restrict___3b59af861bdd (hU : IsAffineOpen U)
    [(F.restrict hU.fromSpec).IsQuasicoherent] : Nonempty (F.restrict U.ι).Presentation := by sorry

alias «GlobalTheory».«QCoh».«nonempty_presentation_restrict_ι» := P2M_GlobalTheory_QCoh_nonempty_presentation_restrict___3b59af861bdd
