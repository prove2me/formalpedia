-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_chart_smul_52f18409990f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_chart_smul_52f18409990f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:01:01.66884+00:00
-- url     : https://prove2.me/theorems/7e441eb0-f984-4b34-9a98-8b3a96845df3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span chart smul 52f18409990f: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span chart smul 52f18409990f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span chart smul 52f18409990f construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Span chart smul 52f18409990f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartSpan.lean#L19-L19

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
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_chart_smul_52f18409990f {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartSpan».«chart_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_chart_smul_52f18409990f
