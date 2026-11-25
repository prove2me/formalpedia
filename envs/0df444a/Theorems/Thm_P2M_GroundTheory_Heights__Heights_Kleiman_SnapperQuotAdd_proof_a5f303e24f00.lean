-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:57:58.754385+00:00
-- url     : https://prove2.me/theorems/3fbefbae-40e0-437d-8030-7b0fb9dff639
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Add proof a5f303e24f00: P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Add proof a5f303e24f00
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Add proof a5f303e24f00 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quot Add proof a5f303e24f00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L176-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L176-L227

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_proof_00587d327cc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c

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
set_option maxHeartbeats 1000000
open SnapperQuotientAdditivity

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00 (hfin : SnapperSubquotFinite.Statement.{u, v, w}) :
    SnapperQuotAdd.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotAdd».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00
