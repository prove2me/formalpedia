-- Prove2me | Theorems.Thm_StrictCQ_Scaled_bounded_multipliers_kkt
-- name    : StrictCQ.Scaled.bounded_multipliers_kkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:44.977106+00:00
-- url     : https://prove2.me/theorems/f1fcc712-e325-410b-b22b-0c934fb04660
-- title:
--   §2, p. 3 — Scaled-AKKT with bounded multipliers implies KKT
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a $C^1$ constraint system on $\mathbb R^n$, $x^*$ a feasible point and $f$ a $C^1$ objective. Let $x^k \to x^*$, $\lambda^k \in \mathbb R^m$ and $\mu^k \in \mathbb R^p_+$ be sequences satisfying (1.3), $\min\{\mu^k_j, -g_j(x^k)\} \to 0$ for every $j$, and (2.2),
--
--   $$
--   \lim_{k\to\infty} \max\{1, \|\lambda^k\|_\infty, \|\mu^k\|_\infty\}^{-1}\, \Big\|\nabla f(x^k) + \sum_{i=1}^m \lambda^k_i \nabla h_i(x^k) + \sum_{j=1}^p \mu^k_j \nabla g_j(x^k)\Big\| = 0 .
--   $$
--
--   If the set $\{\lambda^k, \mu^k : k \in \mathbb N\}$ is bounded, then $x^*$ satisfies KKT for $f$.
--
--   This is the bounded case of the proof that (2.3) is a strict constraint qualification for Scaled-AKKT; it needs no constraint qualification.
--
--   **Formalization Note** Boundedness of the multiplier set is written as boundedness above of $\max\{\|\lambda^k\|_\infty, \|\mu^k\|_\infty\}$ over $k$. The paper's sentence assumes MFCQ as well; the bounded case does not use it, so the hypothesis is omitted.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 3, §2 (bounded case of the proof that (2.3) is a strict CQ)

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem bounded_multipliers_kkt {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Fin m → ℝ) (mu : ℕ → Fin p → ℝ)
    (hx : Tendsto x atTop (𝓝 xs)) (hmu : ∀ k j, 0 ≤ mu k j)
    (h13 : ∀ j, Tendsto (fun k => min (mu k j) (-(C.g j (x k)))) atTop (𝓝 0))
    (h22 : Tendsto (fun k => (max 1 (max ‖lam k‖ ‖mu k‖))⁻¹ *
      ‖gradient f (x k) + ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k)‖) atTop (𝓝 0))
    (hbdd : BddAbove (Set.range fun k => max ‖lam k‖ ‖mu k‖)) :
    C.IsKKT f xs := by sorry

end StrictCQ.Scaled
