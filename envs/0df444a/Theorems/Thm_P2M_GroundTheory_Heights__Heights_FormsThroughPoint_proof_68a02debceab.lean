-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FormsThroughPoint_proof_68a02debceab
-- name    : P2M_GroundTheory_Heights__Heights_FormsThroughPoint_proof_68a02debceab
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:35:38.853328+00:00
-- url     : https://prove2.me/theorems/eb1d7bad-fa20-43e0-949a-1fce6682d78c
-- title:
--   P2 M Ground Theory Heights  Heights Forms Through Point proof 68a02debceab: P2 M Ground Theory Heights  Heights Forms Through Point proof 68a02debceab
-- statement:
--   The P2 M Ground Theory Heights  Heights Forms Through Point proof 68a02debceab construction uses the P2 M Ground Theory Heights  Heights Forms Through Point proof 68a02debceab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFormsThroughPoint.lean#L25-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFormsThroughPoint.lean#L25-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFormsThroughPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_proof_9ab3fe5ffabf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_FormsThroughPoint_proof_68a02debceab (hZ : IncidenceZeroLocus.Statement) (hI : ThroughPointIncIdeal.Statement)
    (hC : ChartZeroTrdeg.Statement) (hT : ThroughTwoPointsTrdeg.Statement)
    (hB : TrdegBaseAlgebraic.Statement) : FormsThroughPoint.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FormsThroughPoint».«proof» := P2M_GroundTheory_Heights__Heights_FormsThroughPoint_proof_68a02debceab
