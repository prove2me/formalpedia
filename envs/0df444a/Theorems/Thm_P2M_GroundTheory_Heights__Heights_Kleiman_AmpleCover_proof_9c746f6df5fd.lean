-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_proof_9c746f6df5fd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_proof_9c746f6df5fd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:44.829427+00:00
-- url     : https://prove2.me/theorems/cd8d501a-7b07-4bc9-b6e8-fe0dab80f9c2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Cover proof 9c746f6df5fd: P2 M Ground Theory Heights  Heights Kleiman Ample Cover proof 9c746f6df5fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Cover proof 9c746f6df5fd construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Cover proof 9c746f6df5fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleCover.lean#L39-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleCover.lean#L39-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleCover
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_proof_9c746f6df5fd : AmpleCover.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleCover».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_proof_9c746f6df5fd
