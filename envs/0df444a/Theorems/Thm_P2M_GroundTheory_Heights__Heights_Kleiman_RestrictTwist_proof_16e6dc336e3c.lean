-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:32:34.063382+00:00
-- url     : https://prove2.me/theorems/7d97b0f5-1980-4f89-a191-0c6391d9b274
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist proof 16e6dc336e3c: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist proof 16e6dc336e3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist proof 16e6dc336e3c construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist proof 16e6dc336e3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L359-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L359-L364

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c : Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_proof_16e6dc336e3c
