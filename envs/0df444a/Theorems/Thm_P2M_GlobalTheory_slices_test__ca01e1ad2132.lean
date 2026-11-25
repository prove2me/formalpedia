-- Prove2me | Theorems.Thm_P2M_GlobalTheory_slices_test__ca01e1ad2132
-- name    : P2M_GlobalTheory_slices_test__ca01e1ad2132
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:55.510795+00:00
-- url     : https://prove2.me/theorems/6aaa933c-5300-4e25-a808-4a96d5894892
-- title:
--   P2 M Global Theory slices test  ca01e1ad2132: P2 M Global Theory slices test  ca01e1ad2132
-- statement:
--   The P2 M Global Theory slices test  ca01e1ad2132 construction uses the P2 M Global Theory slices test  ca01e1ad2132 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyConstantCompactSupportSlicesOperatorApply.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyConstantCompactSupportSlicesOperatorApply.lean#L100-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyConstantCompactSupportSlicesOperatorApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory

theorem P2M_GlobalTheory_slices_test__ca01e1ad2132 : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by sorry

alias «GlobalTheory».«slices_test'» := P2M_GlobalTheory_slices_test__ca01e1ad2132
