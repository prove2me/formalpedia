-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_2
-- name    : StochSQP.Vanishing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:34.964365+00:00
-- url     : https://prove2.me/theorems/3b70ddab-0f9e-4f13-b6f7-5a4ced9ea0cd
-- title:
--   Lemma 2, p. 11 — χ_k and ζ_k are eventually constant, with χ_k ≤ χ_max and ζ_k ≥ ζ_min
-- statement:
--   Fix a problem, valid parameters, an open convex set $X$ on which Assumption 1 holds, and the constants $\kappa_H, \zeta$ of Assumption 3. There exist $\chi_{\max} > 0$ and $\zeta_{\min} > 0$ such that, in any run whose iterates lie in $X$ and whose matrices $H_k$ satisfy Assumption 3 with $\kappa_H, \zeta$, there is an index $k_{\chi,\zeta} \in \mathbb N$ with
--   $$(\chi_k, \zeta_k) = (\chi_{k_{\chi,\zeta}}, \zeta_{k_{\chi,\zeta}}) \ \text{ for all } k \ge k_{\chi,\zeta}, \qquad (\chi_{k_{\chi,\zeta}}, \zeta_{k_{\chi,\zeta}}) \in (0, \chi_{\max}] \times [\zeta_{\min}, \infty).$$
--
--   The adaptive sequences $\{\chi_k\}$ and $\{\zeta_k\}$ that distinguish tangentially from normally dominated search directions therefore stabilize after finitely many iterations, at values bounded uniformly over all runs.
--
--   **Formalization Note.** The constants are quantified before the run and depend only on the problem data, the parameters, $X$, $\kappa_H$ and $\zeta$.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 11, Lemma 2

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_2 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (κH ζH : ℝ) :
    ∃ χmax > (0 : ℝ), ∃ ζmin > (0 : ℝ), ∀ R : Run n m, IsRun P A R → (∀ k, R.x k ∈ X) →
      Assumption3 P R κH ζH →
        ∃ K : ℕ, (∀ k ≥ K, R.χ k = R.χ K ∧ R.ζ k = R.ζ K) ∧
          0 < R.χ K ∧ R.χ K ≤ χmax ∧ ζmin ≤ R.ζ K := by sorry

end StochSQP.Vanishing
