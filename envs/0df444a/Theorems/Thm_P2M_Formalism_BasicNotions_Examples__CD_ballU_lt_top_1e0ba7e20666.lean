-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ballU_lt_top_1e0ba7e20666
-- name    : P2M_Formalism_BasicNotions_Examples__CD_ballU_lt_top_1e0ba7e20666
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:30.082437+00:00
-- url     : https://prove2.me/theorems/02c67be9-9875-49dd-8828-3e3cb94781b6
-- title:
--   P2 M Formalism Basic Notions Examples  CD ball U lt top 1e0ba7e20666: P2 M Formalism Basic Notions Examples  CD ball U lt top 1e0ba7e20666
-- statement:
--   The P2 M Formalism Basic Notions Examples  CD ball U lt top 1e0ba7e20666 construction uses the P2 M Formalism Basic Notions Examples  CD ball U lt top 1e0ba7e20666 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsOmegaLeb.lean#L182-L191

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

theorem P2M_Formalism_BasicNotions_Examples__CD_ballU_lt_top_1e0ba7e20666 (lam : Measure (lieU P Q)) [lam.IsAddHaarMeasure] (r : ℝ) :
    lam (ballU P Q r) < ⊤ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«CD».«ballU_lt_top» := P2M_Formalism_BasicNotions_Examples__CD_ballU_lt_top_1e0ba7e20666
