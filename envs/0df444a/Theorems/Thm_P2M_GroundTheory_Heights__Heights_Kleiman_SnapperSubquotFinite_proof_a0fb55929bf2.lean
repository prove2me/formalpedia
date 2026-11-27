-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotFinite_proof_a0fb55929bf2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotFinite_proof_a0fb55929bf2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:39:18.193959+00:00
-- url     : https://prove2.me/theorems/713cf8d2-29bc-41c3-8390-8573342645af
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Subquot Finite proof a0fb55929bf2: P2 M Ground Theory Heights  Heights Kleiman Snapper Subquot Finite proof a0fb55929bf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Subquot Finite proof a0fb55929bf2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Subquot Finite proof a0fb55929bf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSubquotFinite.lean#L76-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSubquotFinite.lean#L76-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_proof_00587d327cc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00

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
open SnapperQuotientAdditivity SnapperSubquotientFinite

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotFinite_proof_a0fb55929bf2 (hfin : SnapperFinite.Statement.{u, v, w}) :
    SnapperSubquotFinite.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSubquotFinite».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotFinite_proof_a0fb55929bf2
