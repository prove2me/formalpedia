-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_zero_mem_ballU_14f16944d72d
-- name    : P2M_Formalism_BasicNotions_Examples__CD_zero_mem_ballU_14f16944d72d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:37.168734+00:00
-- url     : https://prove2.me/theorems/48359c5d-9f77-416e-87a3-d8db008b8038
-- title:
--   P2 M Formalism Basic Notions Examples  CD zero mem ball U 14f16944d72d: P2 M Formalism Basic Notions Examples  CD zero mem ball U 14f16944d72d
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD zero mem ball U 14f16944d72d construction uses the P2 M Formalism Basic Notions Examples  CD zero mem ball U 14f16944d72d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L173-L175

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q

theorem P2M_Formalism_BasicNotions_Examples__CD_zero_mem_ballU_14f16944d72d {r : ℝ} (hr : 0 < r) : (0 : lieU P Q) ∈ ballU P Q r := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«zero_mem_ballU» := P2M_Formalism_BasicNotions_Examples__CD_zero_mem_ballU_14f16944d72d
