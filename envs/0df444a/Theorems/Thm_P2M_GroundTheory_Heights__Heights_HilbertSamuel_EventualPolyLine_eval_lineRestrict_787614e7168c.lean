-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_eval_lineRestrict_787614e7168c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_eval_lineRestrict_787614e7168c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:09.752844+00:00
-- url     : https://prove2.me/theorems/63c2f9e8-6ddb-4bd8-a540-9e4d1fefad93
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line eval line Restrict 787614e7168c: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line eval line Restrict 787614e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line eval line Restrict 787614e7168c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line eval line Restrict 787614e7168c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L22-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_eval_lineRestrict_787614e7168c [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) (t : ℚ) :
    (lineRestrict a c p).eval t = MvPolynomial.eval (fun k => c k + t * a k) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolyLine».«eval_lineRestrict» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_eval_lineRestrict_787614e7168c
