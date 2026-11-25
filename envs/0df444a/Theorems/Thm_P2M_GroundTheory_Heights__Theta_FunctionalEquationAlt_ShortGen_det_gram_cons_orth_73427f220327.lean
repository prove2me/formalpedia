-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_orth_73427f220327
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_orth_73427f220327
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:05:50.050527+00:00
-- url     : https://prove2.me/theorems/4f246db9-0a16-40c4-bac2-e78a69e07a6d
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram cons orth 73427f220327: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram cons orth 73427f220327
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram cons orth 73427f220327 construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen det gram cons orth 73427f220327 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L198-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L198-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [FiniteDimensional ℝ W]

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_orth_73427f220327 {m : ℕ} (v : W) (c : Fin m → W) (hc : ∀ i, inner ℝ v (c i) = 0) :
    (gram ℝ (Fin.cons v c : Fin (m + 1) → W)).det = ‖v‖ ^ 2 * (gram ℝ c).det := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«det_gram_cons_orth» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_orth_73427f220327
