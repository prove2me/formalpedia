-- Prove2me | Theorems.Thm_RelaxationMethod_FullDim_step_pointwise_closer
-- name    : RelaxationMethod.FullDim.step_pointwise_closer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:25:27.542195+00:00
-- url     : https://prove2.me/theorems/5e5a802e-1b2c-49b1-a58f-107ad6f967b3
-- title:
--   §1 — a step towards a violated half-space is point-wise closer to $A$ (equality on $\pi_j$ for $\lambda = 2$)
-- statement:
--   Let $A = \bigcap_{i=1}^m H_i$ be the nonempty solution polytope of a system of linear inequalities $H_i : \langle a_i, x\rangle + b_i \ge 0$ in $E_n$. Let $p$ be a point with $p \notin H_j$ for some index $j$, let $q$ be the point of $H_j$ nearest to $p$ (the projection of $p$ on the boundary hyperplane $\pi_j : \langle a_j, x\rangle + b_j = 0$), let $0 < \lambda \le 2$ and put $p_1 = p + \lambda (q - p)$. Then $p_1 \ne p$ and
--
--   $$
--   |p_1 - a| \le |p - a| \qquad \text{for all } a \in A .
--   $$
--
--   If $0 < \lambda < 2$ (so $p_1$ lies strictly between $p$ and the mirror image $p'$ of $p$ in $\pi_j$) the inequality is strict for every $a \in A$: $p_1$ is point-wise closer than $p$ to $A$ in the sense of (1.1). If $\lambda = 2$ (so $p_1 = p'$) then, for $a \in A$, equality $|p_1 - a| = |p - a|$ holds exactly when $a$ lies on $\pi_j$.
--
--   This is the basic monotonicity of the relaxation method: every step, in particular the step (1.5)–(1.7) towards a farthest half-space, moves towards every solution of the system.
--
--   **Formalization Note** The paper states the claim for any violated half-space $H_j$ and a point $p_1$ on the segment from $p$ to $p'$; we state it in that generality, with $q$ given as a nearest point of $H_j$ (as in (1.6)), so it applies to every relaxation step (1.5)–(1.7). The claim $p_1 \ne p$ is condition (2.1) of Fejér-monotonicity. For $\lambda = 2$ we state the page's "with the exception that we have the equality sign for the points of $A$ which are on the boundary of $H_j$" as an equivalence. The parameter $\lambda$ is named `lam`.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), pp. 393–394, §1

import Mathlib
import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
open Filter Topology

namespace RelaxationMethod.FullDim

/-- §1, pp. 393–394: let `p ∉ H_j` for some `j`, let `q` be the point of `H_j` nearest to `p`
(the projection of `p` on the boundary hyperplane `π_j`), and let `p₁ = p + lam (q - p)` with
`0 < lam ≤ 2`. Then `p₁ ≠ p` and `|p₁ - a| ≤ |p - a|` for every `a` of the (nonempty)
polytope `A`. For `0 < lam < 2` the new point `p₁` is point-wise closer than `p` to `A` in the
sense of (1.1). For `lam = 2` (`p₁ = p′`, the mirror image of `p` in `π_j`) (1.1) again holds,
except that equality holds exactly at the points of `A` on the boundary `π_j` of `H_j`. -/
theorem step_pointwise_closer {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p q : EuclideanSpace ℝ (Fin n)) (j : Fin m) (hpj : p ∉ halfSpace (a j) (b j))
    (hq : q ∈ halfSpace (a j) (b j))
    (hpq : dist p q = Metric.infDist p (halfSpace (a j) (b j))) :
    p + lam • (q - p) ≠ p ∧
      (∀ x ∈ polytope a b, dist (p + lam • (q - p)) x ≤ dist p x) ∧
      (lam < 2 → IsPointwiseCloser (polytope a b) p (p + lam • (q - p))) ∧
      (lam = 2 → ∀ x ∈ polytope a b,
        (dist (p + lam • (q - p)) x = dist p x ↔ inner ℝ (a j) x + b j = 0)) := by sorry

end RelaxationMethod.FullDim
