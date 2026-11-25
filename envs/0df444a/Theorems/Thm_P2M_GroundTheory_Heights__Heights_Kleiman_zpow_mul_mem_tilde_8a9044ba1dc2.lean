-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_zpow_mul_mem_tilde_8a9044ba1dc2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_zpow_mul_mem_tilde_8a9044ba1dc2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:06:42.040652+00:00
-- url     : https://prove2.me/theorems/f1be4a6b-684d-5ffe-accd-880625638c8e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman zpow mul mem tilde 8a9044ba1dc2: P2 M Ground Theory Heights  Heights Kleiman zpow mul mem tilde 8a9044ba1dc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman zpow mul mem tilde 8a9044ba1dc2 construction uses the P2 M Ground Theory Heights  Heights Kleiman zpow mul mem tilde 8a9044ba1dc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L20-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L20-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_zpow_mul_mem_tilde_8a9044ba1dc2 (M : FinGradedSub (S := S) (x := x) Ω) {I : Chart x} {i : Fin (N + 1)}
    (hi : i ∈ I.1) (c d : ℤ) {y : Ω} (hy : y ∈ M.tilde d I) : x i ^ c * y ∈ M.tilde (d + c) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«zpow_mul_mem_tilde» := P2M_GroundTheory_Heights__Heights_Kleiman_zpow_mul_mem_tilde_8a9044ba1dc2
