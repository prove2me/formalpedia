-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_proof_e53ace07c4b8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_proof_e53ace07c4b8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:37.213848+00:00
-- url     : https://prove2.me/theorems/9d2eda44-418a-5e9c-98bb-dd30c714017e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span proof e53ace07c4b8: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span proof e53ace07c4b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span proof e53ace07c4b8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span proof e53ace07c4b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L62-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L62-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartSpan
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_proof_1c887bca4a14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_proof_e53ace07c4b8 : VeryAmpleZChartSpan.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartSpan».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_proof_e53ace07c4b8
