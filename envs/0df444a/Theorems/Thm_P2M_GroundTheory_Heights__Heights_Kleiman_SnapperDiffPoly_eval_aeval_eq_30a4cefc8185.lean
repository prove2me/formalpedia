-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:35.12999+00:00
-- url     : https://prove2.me/theorems/9a3cf3dc-a1e6-4af6-b469-c562d65c8397
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly eval aeval eq 30a4cefc8185: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly eval aeval eq 30a4cefc8185
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly eval aeval eq 30a4cefc8185 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly eval aeval eq 30a4cefc8185 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L17-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185 {K : Type} (x : K → ℚ) (σ : K → MvPolynomial K ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval σ P) = eval (fun k => eval x (σ k)) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«eval_aeval_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
