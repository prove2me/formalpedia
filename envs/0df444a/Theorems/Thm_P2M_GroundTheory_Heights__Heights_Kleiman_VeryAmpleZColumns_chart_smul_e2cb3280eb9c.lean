-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_chart_smul_e2cb3280eb9c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_chart_smul_e2cb3280eb9c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:52.353437+00:00
-- url     : https://prove2.me/theorems/05111df0-15d2-44fa-81b2-c40da4648f95
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns chart smul e2cb3280eb9c: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns chart smul e2cb3280eb9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns chart smul e2cb3280eb9c construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns chart smul e2cb3280eb9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L20-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_chart_smul_e2cb3280eb9c {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZColumns».«chart_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_chart_smul_e2cb3280eb9c
