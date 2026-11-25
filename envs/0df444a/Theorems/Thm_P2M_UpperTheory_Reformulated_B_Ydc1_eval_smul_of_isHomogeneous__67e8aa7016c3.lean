-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3
-- name    : P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:46.38153+00:00
-- url     : https://prove2.me/theorems/5241e7dd-f469-46d3-8ad1-31fcfbb05484
-- title:
--   P2 M Upper Theory Reformulated B Ydc1 eval smul of is Homogeneous  67e8aa7016c3: P2 M Upper Theory Reformulated B Ydc1 eval smul of is Homogeneous  67e8aa7016c3
-- statement:
--   The P2 M Upper Theory Reformulated B Ydc1 eval smul of is Homogeneous  67e8aa7016c3 construction uses the P2 M Upper Theory Reformulated B Ydc1 eval smul of is Homogeneous  67e8aa7016c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalSmulOfIsHomogeneousAlt.lean#L3-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalSmulOfIsHomogeneousAlt.lean#L3-L17

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3.{u_1} :
    ∀ {τ : Type u_1} {φ : MvPolynomial τ ℂ} {n : ℕ},
      φ.IsHomogeneous n →
        ∀ (c : ℂ) (w : τ → ℂ),
          (MvPolynomial.eval (c • w) : MvPolynomial τ ℂ → ℂ) φ = c ^ n * (MvPolynomial.eval w : MvPolynomial τ ℂ → ℂ) φ := by sorry

alias «UpperTheory».«Reformulated».«B».«Ydc1».«eval_smul_of_isHomogeneous».«» := P2M_UpperTheory_Reformulated_B_Ydc1_eval_smul_of_isHomogeneous__67e8aa7016c3
