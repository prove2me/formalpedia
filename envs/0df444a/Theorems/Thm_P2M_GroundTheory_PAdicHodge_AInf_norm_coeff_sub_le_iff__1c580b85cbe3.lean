-- Prove2me | Theorems.Thm_P2M_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff__1c580b85cbe3
-- name    : P2M_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff__1c580b85cbe3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:44.937168+00:00
-- url     : https://prove2.me/theorems/ee3b3997-d268-4b42-8b5a-cf6520e48fff
-- title:
--   P2 M Ground Theory PAdic Hodge AInf norm coeff sub le iff  1c580b85cbe3: P2 M Ground Theory PAdic Hodge AInf norm coeff sub le iff  1c580b85cbe3
-- statement:
--   The P2 M Ground Theory PAdic Hodge AInf norm coeff sub le iff  1c580b85cbe3 construction uses the P2 M Ground Theory PAdic Hodge AInf norm coeff sub le iff  1c580b85cbe3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L93-L96

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p

theorem P2M_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff__1c580b85cbe3 (ϖ : 𝒪♭) (k : ℕ) (x y : AInf K p) :
    (∀ i, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ k) ↔ ∀ i, ‖(x - y).coeff i‖ ≤ ‖ϖ‖ ^ k := by sorry

alias «GroundTheory».«PAdicHodge».«AInf».«norm_coeff_sub_le_iff'» := P2M_GroundTheory_PAdicHodge_AInf_norm_coeff_sub_le_iff__1c580b85cbe3
