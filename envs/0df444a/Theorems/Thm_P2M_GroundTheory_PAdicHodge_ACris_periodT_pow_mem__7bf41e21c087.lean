-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_ACris_periodT_pow_mem__7bf41e21c087
-- name    : P2M_GroundTheory_PAdicHodge_ACris_periodT_pow_mem__7bf41e21c087
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:44.632904+00:00
-- url     : https://prove2.me/theorems/7ced1d70-80e8-475f-b314-1052a95be283
-- title:
--   P2 M Ground Theory PAdic Hodge ACris period T pow mem  7bf41e21c087: P2 M Ground Theory PAdic Hodge ACris period T pow mem  7bf41e21c087
-- statement:
--   The P2 M Ground Theory PAdic Hodge ACris period T pow mem  7bf41e21c087 construction uses the P2 M Ground Theory PAdic Hodge ACris period T pow mem  7bf41e21c087 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L268-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L268-L285

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}

theorem P2M_GroundTheory_PAdicHodge_ACris_periodT_pow_mem__7bf41e21c087 {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : periodT hε ^ (p - 1) ∈ 𝔭 := by sorry

alias «GroundTheory».«PAdicHodge».«ACris».«periodT_pow_mem'» := P2M_GroundTheory_PAdicHodge_ACris_periodT_pow_mem__7bf41e21c087
