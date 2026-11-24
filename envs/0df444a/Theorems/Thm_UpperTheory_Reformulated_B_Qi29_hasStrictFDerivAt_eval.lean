-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qi29_hasStrictFDerivAt_eval
-- name    : UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:33.298157+00:00
-- url     : https://prove2.me/theorems/6f532cb5-721c-48bc-bbc1-326ab8404b62
-- title:
--   Qi29: has Strict FDeriv At eval
-- statement:
--   The Qi29 construction uses the has Strict FDeriv At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HasStrictFDerivAtEval.lean#L11-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HasStrictFDerivAtEval.lean#L11-L49

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)),
      HasStrictFDerivAt
        (fun (y : EuclideanSpace ℂ (Fin n)) ↦ (MvPolynomial.eval fun (i : Fin n) ↦ y.ofLp i : MvPolynomial (Fin n) ℂ → ℂ) p)
        (UpperTheory.Reformulated.B.Qi29.polyDeriv p x) x := by sorry
