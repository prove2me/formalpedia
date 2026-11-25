-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_idx_isEmpty_3f8167bd3da0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_idx_isEmpty_3f8167bd3da0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:58:18.026455+00:00
-- url     : https://prove2.me/theorems/e648c967-b00c-461f-9c24-36ee2fe39cdf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity idx is Empty 3f8167bd3da0: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity idx is Empty 3f8167bd3da0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity idx is Empty 3f8167bd3da0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity idx is Empty 3f8167bd3da0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L90-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_idx_isEmpty_3f8167bd3da0 {Ω : Type w} [Field Ω] {N : ℕ} (x : Fin (N + 1) → Ω) : IsEmpty (Cech.Idx (support x) (N + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«idx_isEmpty» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_idx_isEmpty_3f8167bd3da0
