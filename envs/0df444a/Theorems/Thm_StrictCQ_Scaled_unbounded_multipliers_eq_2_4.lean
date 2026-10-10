-- Prove2me | Theorems.Thm_StrictCQ_Scaled_unbounded_multipliers_eq_2_4
-- name    : StrictCQ.Scaled.unbounded_multipliers_eq_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:35.167529+00:00
-- url     : https://prove2.me/theorems/0199fb63-41f3-4f34-924f-1ef29a75c802
-- title:
--   §2, pp. 3–4, (2.4) — unbounded Scaled-AKKT multipliers give a nonzero solution of (2.4)
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a $C^1$ constraint system on $\mathbb R^n$, $x^*$ a feasible point and $f$ a $C^1$ objective. Let $x^k \to x^*$, $\lambda^k \in \mathbb R^m$ and $\mu^k \in \mathbb R^p_+$ be sequences satisfying (1.3) and (2.2), as in the Scaled-AKKT condition, and suppose the set $\{\lambda^k, \mu^k : k \in \mathbb N\}$ is unbounded. Then there exist $\lambda \in \mathbb R^m$ and $\mu \in \mathbb R^p_+$ with $\mu_j = 0$ whenever $g_j(x^*) \ne 0$ and $\max\{\|\lambda\|_\infty, \|\mu\|_\infty\} = 1$ such that
--
--   $$
--   \sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j:\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) = 0 \qquad (2.4).
--   $$
--
--   This is the unbounded case of the proof that (2.3) is a strict constraint qualification for Scaled-AKKT: normalized multipliers have a nonzero limit that annihilates the active gradients.
--
--   **Formalization Note** Unboundedness is the failure of boundedness above of $\max\{\|\lambda^k\|_\infty, \|\mu^k\|_\infty\}$. The sum in (2.4) is written over all $j$ with $\mu_j = 0$ off the active set.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 3–4, §2, (2.4)

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem unbounded_multipliers_eq_2_4 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ)
    (hx : Tendsto x atTop (𝓝 xs)) (hmu : ∀ k j, 0 ≤ mu k j)
    (h13 : ∀ j, Tendsto (fun k => min (mu k j) (-(C.g j (x k)))) atTop (𝓝 0))
    (h22 : Tendsto (fun k => (max 1 (max ‖lam k‖ ‖mu k‖))⁻¹ *
      ‖gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k)‖) atTop (𝓝 0))
    (hunbdd : ¬ BddAbove (Set.range fun k => max ‖lam k‖ ‖mu k‖)) :
    ∃ (l : Fin m → ℝ) (u : Fin p → ℝ), (∀ j, 0 ≤ u j) ∧ (∀ j, C.g j xs ≠ 0 → u j = 0) ∧
      max ‖l‖ ‖u‖ = 1 ∧
      ∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs = 0 := by sorry

end StrictCQ.Scaled
