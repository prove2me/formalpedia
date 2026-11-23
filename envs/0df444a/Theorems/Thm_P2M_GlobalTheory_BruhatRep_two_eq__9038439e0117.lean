-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BruhatRep_two_eq__9038439e0117
-- name    : P2M_GlobalTheory_BruhatRep_two_eq__9038439e0117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:53.821467+00:00
-- url     : https://prove2.me/theorems/b7aa4b5c-a947-48f7-943f-e5fd19a8ac96
-- title:
--   P2 M Global Theory Bruhat Rep two eq  9038439e0117: P2 M Global Theory Bruhat Rep two eq  9038439e0117
-- statement:
--   The P2 M Global Theory Bruhat Rep two eq  9038439e0117 construction uses the P2 M Global Theory Bruhat Rep two eq  9038439e0117 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L115-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)

theorem P2M_GlobalTheory_BruhatRep_two_eq__9038439e0117 {a a' b b' : K} (ha : a = a') (hb : b = b') :
    mx m a * n b = mx m a' * n b' := by sorry

alias «GlobalTheory».«BruhatRep».«two_eq'» := P2M_GlobalTheory_BruhatRep_two_eq__9038439e0117
