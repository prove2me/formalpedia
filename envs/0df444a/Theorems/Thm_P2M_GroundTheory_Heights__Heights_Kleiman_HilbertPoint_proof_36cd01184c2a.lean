-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_proof_36cd01184c2a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_proof_36cd01184c2a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:49.454334+00:00
-- url     : https://prove2.me/theorems/175f74df-0085-46f0-b9a2-3c4e1e0f1bc0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point proof 36cd01184c2a: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point proof 36cd01184c2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point proof 36cd01184c2a construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point proof 36cd01184c2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L216-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L216-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_proof_36cd01184c2a : HilbertPoint.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_proof_36cd01184c2a
