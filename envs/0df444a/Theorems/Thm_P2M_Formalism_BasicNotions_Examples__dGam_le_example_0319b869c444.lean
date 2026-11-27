-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__dGam_le_example_0319b869c444
-- name    : P2M_Formalism_BasicNotions_Examples__dGam_le_example_0319b869c444
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:16.426704+00:00
-- url     : https://prove2.me/theorems/f152085c-e4e7-5ce8-92df-dbc7395dfd00
-- title:
--   P2 M Formalism Basic Notions Examples  d Gam le example 0319b869c444: P2 M Formalism Basic Notions Examples  d Gam le example 0319b869c444
-- statement:
--   The P2 M Formalism Basic Notions Examples  d Gam le example 0319b869c444 construction uses the P2 M Formalism Basic Notions Examples  d Gam le example 0319b869c444 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/FmZeroHLatEmpty.lean#L257-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/FmZeroHLatEmpty.lean#L257-L261

import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_FmZeroHLatEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField Formalism.BasicNotions

theorem P2M_Formalism_BasicNotions_Examples__dGam_le_example_0319b869c444 {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    (C : ColumnChain R Tau hc) (h : C.DGam = 1) :
    Real.log (C.DGam : ℝ) ≤ 0 * R.f * R.N R.m * Real.log ((R.f : ℝ) * R.N R.m) := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«dGam_le_example» := P2M_Formalism_BasicNotions_Examples__dGam_le_example_0319b869c444
