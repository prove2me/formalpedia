-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_prod_mem_pow_1dbdeee6f1d5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_prod_mem_pow_1dbdeee6f1d5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:50.941795+00:00
-- url     : https://prove2.me/theorems/1c3f2b8e-76a4-4177-a133-11386a8e5aab
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span prod mem pow 1dbdeee6f1d5: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span prod mem pow 1dbdeee6f1d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span prod mem pow 1dbdeee6f1d5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span prod mem pow 1dbdeee6f1d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L21-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartSpan
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_prod_mem_pow_1dbdeee6f1d5 (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartSpan».«prod_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_prod_mem_pow_1dbdeee6f1d5
