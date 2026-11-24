-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc
-- name    : P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:30.322383+00:00
-- url     : https://prove2.me/theorems/82a8bf97-ad82-4fc3-b37a-07f0d2c72b17
-- title:
--   P2 M Ground Theory Heights  Heights continuous At norm Sq eval c614db76f4fc: P2 M Ground Theory Heights  Heights continuous At norm Sq eval c614db76f4fc
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous At norm Sq eval c614db76f4fc construction uses the P2 M Ground Theory Heights  Heights continuous At norm Sq eval c614db76f4fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L30-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
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
open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    ContinuousAt (fun z => ‖eval z Q‖ ^ 2) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuousAt_normSq_eval» := P2M_GroundTheory_Heights__Heights_continuousAt_normSq_eval_c614db76f4fc
