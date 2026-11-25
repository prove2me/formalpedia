-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incidence_point_247b5a18c1c3
-- name    : P2M_GroundTheory_Heights__Heights_mem_incidence_point_247b5a18c1c3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:40.965826+00:00
-- url     : https://prove2.me/theorems/35f2efa0-34eb-4eba-b08c-c04b24704011
-- title:
--   P2 M Ground Theory Heights  Heights mem incidence point 247b5a18c1c3: P2 M Ground Theory Heights  Heights mem incidence point 247b5a18c1c3
-- statement:
--   The P2 M Ground Theory Heights  Heights mem incidence point 247b5a18c1c3 construction uses the P2 M Ground Theory Heights  Heights mem incidence point 247b5a18c1c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L293-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Statements.lean#L293-L308

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_mem_incidence_point_247b5a18c1c3 {F : Type*} [Field F] (u : Fin 1 × Fin 1 → AlgebraicClosure F) :
    u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 1) F)) 1 ↔ u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_incidence_point» := P2M_GroundTheory_Heights__Heights_mem_incidence_point_247b5a18c1c3
