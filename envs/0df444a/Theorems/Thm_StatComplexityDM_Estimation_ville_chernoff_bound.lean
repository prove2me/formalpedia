-- Prove2me | Theorems.Thm_StatComplexityDM_Estimation_ville_chernoff_bound
-- name    : StatComplexityDM.Estimation.ville_chernoff_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:36.859053+00:00
-- url     : https://prove2.me/theorems/331b8459-5042-4f90-8df5-e240064b7dce
-- title:
--   Lemma A.4, p. 70 — an anytime conditional moment bound
-- statement:
--   Let $Z$ be finite, $K_t(\cdot\mid z_{<t})$ a history-dependent probability kernel, and $X_t(z_{<t},z_t)$ any real-valued adapted process. For every $\delta>0$, the probability that the following inequality fails at any horizon $0\le n\le T$ is at most $\delta$:
--   $$
--   \sum_{t=0}^{n-1}X_t\le
--   \sum_{t=0}^{n-1}\log\!\left(\sum_{w\in Z}K_t(w\mid z_{<t})e^{X_t(z_{<t},w)}\right)+\log(1/\delta).
--   $$
--
--   This supplies simultaneous conditional-moment control for the paper's high-probability estimation result.
--
--   **Formalization Note** Bad-path probability is a sum under the full sequential law. Violation uses a strict inequality. Rounds are 0-based and $n=0$ is included.
-- source:
--   arXiv:2112.13487v3, Lemma A.4, (92), p. 70

import Mathlib
import Definitions.Def_StatComplexityDM_Estimation_Sequential

namespace StatComplexityDM.Estimation

open Classical

/-- Lemma A.4 (92), p. 70, in a finite sequential probability space. -/
theorem ville_chernoff_bound {Z : Type*} [Fintype Z] {T : ℕ}
    (K : (t : Fin T) → Hist Z t.val → Z → ℝ)
    (Xs : (t : Fin T) → Hist Z t.val → Z → ℝ)
    (hK : IsKernel K) (δ : ℝ) (hδ : 0 < δ) :
    (∑ z : Hist Z T,
      if ∃ n : ℕ, n ≤ T ∧
          (∑ t : Fin T, if t.val < n then Xs t (histPrefix z t) (z t) else 0) >
          (∑ t : Fin T, if t.val < n then
            Real.log (∑ w, K t (histPrefix z t) w *
              Real.exp (Xs t (histPrefix z t) w)) else 0) + Real.log (1 / δ)
      then seqLaw K z else 0) ≤ δ := by sorry

end StatComplexityDM.Estimation
