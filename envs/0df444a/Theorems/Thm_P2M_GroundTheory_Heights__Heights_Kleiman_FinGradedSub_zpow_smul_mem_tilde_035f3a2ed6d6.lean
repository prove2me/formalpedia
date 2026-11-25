-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_zpow_smul_mem_tilde_035f3a2ed6d6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_zpow_smul_mem_tilde_035f3a2ed6d6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:49.230132+00:00
-- url     : https://prove2.me/theorems/36bf7af7-6289-4857-a303-5f52588bd4f7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub zpow smul mem tilde 035f3a2ed6d6: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub zpow smul mem tilde 035f3a2ed6d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub zpow smul mem tilde 035f3a2ed6d6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub zpow smul mem tilde 035f3a2ed6d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeShift.lean#L20-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeShift.lean#L20-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeShiftSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeShift
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_zpow_smul_mem_tilde_035f3a2ed6d6 (M : FinGradedSub (S := S) (x := x) E) {I : Chart x}
    {i : Fin (N + 1)} (hi : i ∈ I.1) (c d : ℤ) {y : E} (hy : y ∈ M.tilde d I) :
    x i ^ c • y ∈ M.tilde (d + c) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«zpow_smul_mem_tilde» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_zpow_smul_mem_tilde_035f3a2ed6d6
