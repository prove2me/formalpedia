-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CycleSplit_proof_9966175675a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CycleSplit_proof_9966175675a8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:28:51.323525+00:00
-- url     : https://prove2.me/theorems/baef83aa-ce2d-5d0f-8471-4d2b33a58e03
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cycle Split proof 9966175675a8: P2 M Ground Theory Heights  Heights Kleiman Cycle Split proof 9966175675a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cycle Split proof 9966175675a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cycle Split proof 9966175675a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L83-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L83-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit
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
universe u w
open Classical

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CycleSplit_proof_9966175675a8 (hF : CycleSplit.Filt.Statement.{u, w}) (hCu : CycleSplit.Curve.Statement.{u, w})
    (hSm : CycleSplit.Small.Statement.{u, w}) : CycleSplit.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CycleSplit».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_CycleSplit_proof_9966175675a8
