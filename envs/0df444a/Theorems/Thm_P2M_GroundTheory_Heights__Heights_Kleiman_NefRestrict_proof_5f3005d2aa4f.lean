-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:33:48.569794+00:00
-- url     : https://prove2.me/theorems/d0bf394a-701e-5d01-91b7-cc00664c3573
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Nef Restrict proof 5f3005d2aa4f: P2 M Ground Theory Heights  Heights Kleiman Nef Restrict proof 5f3005d2aa4f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Nef Restrict proof 5f3005d2aa4f construction uses the P2 M Ground Theory Heights  Heights Kleiman Nef Restrict proof 5f3005d2aa4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefRestrict.lean#L27-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefRestrict.lean#L27-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
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
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«NefRestrict».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_NefRestrict_proof_5f3005d2aa4f
