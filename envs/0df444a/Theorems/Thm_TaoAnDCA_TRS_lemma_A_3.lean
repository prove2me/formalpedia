-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_lemma_A_3
-- name    : TaoAnDCA.TRS.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:55.513523+00:00
-- url     : https://prove2.me/theorems/4c5aec02-b976-4c24-9124-6b2bddf8076e
-- title:
--   Lemma A.3, p. 503 — x^k → x*, bounded y^k ∈ ∂h(x^k) and ∂h(x*) ≠ ∅ give h(x^k) → h(x*)
-- statement:
--   Let $h\in\Gamma_0(\mathbb R^n)$ and let $\{x^k\}$ be a sequence in $\mathbb R^n$ such that
--   1. $x^k\to x^*$;
--   2. there is a bounded sequence $\{y^k\}$ with $y^k\in\partial h(x^k)$ for every $k$;
--   3. $\partial h(x^*)$ is nonempty.
--
--   Then
--   $$\lim_{k\to+\infty} h(x^k) = h(x^*).$$
--
--   Lower semicontinuity alone only gives $\liminf h(x^k)\ge h(x^*)$; the lemma supplies the continuity of $h$ along the DCA iterates that is needed to pass to the limit in the proof of Theorem 3.7(iv).
--
--   **Formalization Note.** Values are in `EReal`; hypotheses 2 and 3 make $h(x^k)$ and $h(x^*)$ finite, and the limit is taken in `EReal`.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 503, Appendix, Lemma A.3

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem lemma_A_3 {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (hh : ThreeOpSplitting.ConvexRates.IsProperClosedConvex h)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (xs : EuclideanSpace ℝ (Fin n)) (hx : Tendsto x atTop (𝓝 xs))
    (hy : Bornology.IsBounded (Set.range y)) (hyx : ∀ k, y k ∈ TaoAnDCA.GlobalOpt.subdiff h (x k))
    (hne : (TaoAnDCA.GlobalOpt.subdiff h xs).Nonempty) :
    Tendsto (fun k => h (x k)) atTop (𝓝 (h xs)) := by sorry

end TaoAnDCA.TRS
