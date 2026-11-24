-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_castLE_f986c713271f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_castLE_f986c713271f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:58.40238+00:00
-- url     : https://prove2.me/theorems/658a0393-a70a-499a-abd3-0d979b2b2b04
-- title:
--   P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift cast LE f986c713271f: P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift cast LE f986c713271f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift cast LE f986c713271f construction uses the P2 M Ground Theory Heights  Heights Regular Exp Quad log Lift cast LE f986c713271f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L165-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PExpExtension.lean#L165-L167

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)

theorem P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_castLE_f986c713271f (z : Fin n → ℂ) (i : Fin a) :
    logLift a z (Fin.castLE P.a_le i) = Complex.log (z (Fin.castLE P.a_le i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«ExpQuad».«logLift_castLE» := P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_logLift_castLE_f986c713271f
