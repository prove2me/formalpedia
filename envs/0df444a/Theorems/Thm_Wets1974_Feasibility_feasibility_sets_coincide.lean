-- Prove2me | Theorems.Thm_Wets1974_Feasibility_feasibility_sets_coincide
-- name    : Wets1974.Feasibility.feasibility_sets_coincide
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:31:25.616516+00:00
-- url     : https://prove2.me/theorems/05966e2f-f662-4b3e-8607-dc893e697264
-- title:
--   Theorem 4.1 — the feasibility sets $K_2^\mu$, $K_2^p$, $K_2^s$ coincide under weak covariance
-- statement:
--   Consider a stochastic program with fixed recourse (2.1): a fixed $\bar m \times \bar n$ recourse matrix $W$ and random data $\xi = (c, q, p, T)$ with law $\mu$, a probability measure. Let $Q(x,\xi) = \min\{q(\xi)y \mid Wy = p(\xi) - T(\xi)x,\ y \ge 0\}$ (with value $+\infty$ when infeasible and $-\infty$ when unbounded), $\mathcal Q(x) = E_\xi\{Q(x,\xi)\}$ the expected recourse computed with the paper's extended integral (in which $(+\infty) + (-\infty) = +\infty$), and $\tilde\Xi$ the support of $\mu$. Consider the three feasibility sets
--
--   1. $K_2^\mu = \{x \mid \text{with probability } 1\ \exists y \ge 0,\ Wy = p(\xi) - T(\xi)x\}$,
--   2. $K_2^p = \{x \mid \forall \xi \in \tilde\Xi\ \exists y \ge 0,\ Wy = p(\xi) - T(\xi)x\}$,
--   3. $K_2^s = \{x \mid \mathcal Q(x) < +\infty\}$.
--
--   Assume that $\xi$ satisfies the weak covariance condition of Definition 2.2 (all $c_j$, $q_j p_i$ and $q_j t_{ik}$ are integrable) and that $W$ has full row rank $\bar m$. Then
--
--   $$
--   K_2^\mu = K_2^p = K_2^s.
--   $$
--
--   The theorem says that the probabilistic, the support-based and the finite-expected-cost notions of second-stage feasibility agree, so the region where the deterministic equivalent program is finite can be described pointwise on the support.
--
--   **Formalization Note.** The paper writes "such as Definition 2.2"; the statement uses Definition 2.2 itself. The full row rank of $W$ is the paper's standing assumption ("Without loss of generality, we can assume that $W$ has full rank", p. 312); the result remains true without it. $K_2^\mu$ is taken in its first form on p. 314 ($\exists y \ge 0$ almost surely). The paper's remark that $Q(x,\cdot)$ is measurable (p. 313) is a provable fact and is not added as a hypothesis.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 315, Theorem 4.1 (Eq. (4.2)); sets defined on p. 314; standing full-rank assumption on W, p. 312

import Mathlib
import Definitions.Def_Wets1974_Feasibility_Model

namespace Wets1974.Feasibility

open MeasureTheory

/-- Theorem 4.1, p. 315: under the weak covariance condition (Definition 2.2) and the standing
assumption that `W` has full row rank (p. 312), `K₂^μ = K₂^p = K₂^s`. -/
theorem feasibility_sets_coincide {n nb mb : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (W : Matrix (Fin mb) (Fin nb) ℝ)
    (hW : W.rank = mb) (hcov : WeakCovariance μ) :
    K2mu μ W = K2supp μ W ∧ K2supp μ W = K2s μ W := by sorry

end Wets1974.Feasibility
