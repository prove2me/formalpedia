-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TildeShift_proof_a3c21ad26a82
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TildeShift_proof_a3c21ad26a82
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:27.812+00:00
-- url     : https://prove2.me/theorems/6281550f-a800-546d-9ec7-d469efca58e7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Tilde Shift proof a3c21ad26a82: P2 M Ground Theory Heights  Heights Kleiman Tilde Shift proof a3c21ad26a82
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Tilde Shift proof a3c21ad26a82 construction uses the P2 M Ground Theory Heights  Heights Kleiman Tilde Shift proof a3c21ad26a82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeShift.lean#L48-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeShift.lean#L48-L72

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TildeShift_proof_a3c21ad26a82 : TildeShift.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TildeShift».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_TildeShift_proof_a3c21ad26a82
