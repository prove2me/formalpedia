-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_HomogeneousEvalSmul_eval_smul_of_isHomogeneous
-- name    : UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:43.630414+00:00
-- url     : https://prove2.me/theorems/eb1f64e6-e773-4711-a150-4568ebba2b69
-- title:
--   Homogeneous Eval Smul: eval smul of is Homogeneous
-- statement:
--   The Homogeneous Eval Smul construction uses the eval smul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalSmulOfIsHomogeneous.lean#L3-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalSmulOfIsHomogeneous.lean#L3-L17

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by sorry
