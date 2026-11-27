-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperFinite_proof_2b7bff64732d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperFinite_proof_2b7bff64732d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:16.809039+00:00
-- url     : https://prove2.me/theorems/33dbff4f-9d0b-59f6-bcb9-0e42bf7dc926
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Finite proof 2b7bff64732d: P2 M Ground Theory Heights  Heights Kleiman Snapper Finite proof 2b7bff64732d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Finite proof 2b7bff64732d construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Finite proof 2b7bff64732d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperFinite.lean#L17-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperFinite.lean#L17-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeShiftSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ClaimVanish_proof_dce3cf61647f

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperFinite_proof_2b7bff64732d (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperFinite».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperFinite_proof_2b7bff64732d
