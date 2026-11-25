-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_molli_contDiffAt_433d4d156768
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_molli_contDiffAt_433d4d156768
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:14.795917+00:00
-- url     : https://prove2.me/theorems/d841c20c-b9a2-5765-9ee3-bb12a5cd7963
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas molli cont Diff At 433d4d156768: P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas molli con
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas molli cont Diff At 433d4d156768 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit Argument Convergence Lemmas molli cont Diff At 433d4d156768 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/NormIteratedFDerivCompLeOfIsOpen.lean#L19-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_contDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_molli_contDiffAt_433d4d156768 {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«ArgumentConvergenceLemmas».«molli_contDiffAt» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_molli_contDiffAt_433d4d156768
