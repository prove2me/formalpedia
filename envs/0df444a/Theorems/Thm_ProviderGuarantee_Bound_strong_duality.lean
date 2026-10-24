-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_strong_duality
-- name    : ProviderGuarantee.Bound.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:51.389134+00:00
-- url     : https://prove2.me/theorems/f6beb869-f83a-4ddf-85a3-3e9fc413454e
-- title:
--   Proof of Theorem 1, p. 38 — strong duality between the linear program (14) and its dual (15)
-- statement:
--   Let $n \ge 1$ and let $\gamma \in \mathbb R^n$ have positive entries. The dual of the linear program (14) is the program (15) (p. 38) in the variables $s \in \mathbb R$ and $\lambda \in \mathbb R^{n\times n}$:
--
--   $$\begin{aligned} \text{minimize}\quad & s \\ \text{subject to}\quad & s\gamma_i + \sum_{j=1}^n \lambda_{ij} \ge \gamma_i \quad (i \in N), \\ & \gamma_j - \gamma_k + s\gamma_k - \sum_{i \ne k} \lambda_{ij} \ge 0 \quad (k, j \in N), \\ & \gamma_j \ge \sum_{i=1}^n \lambda_{ij} \quad (j \in N), \qquad \lambda_{ij} \ge 0 \quad (i, j \in N). \end{aligned}$$
--
--   Strong duality holds:
--   1. (weak duality) the objective of every feasible point of (14) is at most $s$ for every feasible $(s, \lambda)$ of (15);
--   2. (14) has an optimal solution;
--   3. (15) has an optimal solution;
--   4. the optimal values are equal: $V(\gamma) = f(\gamma)$, where $f(\gamma)$ is the optimal value of (15).
--
--   The page rewrites (15) as problem (16) by eliminating $s$; $f(\gamma)$, the common value, is the function whose behaviour over $\gamma \in [\gamma_{\min}, \gamma_{\max}]^n$ decides the bound.
--
--   **Formalization Note** $V(\gamma)$ is `lpValue γ` and $f(\gamma)$ is `dualValue γ`, the infimum of $s$ over the feasible pairs of (15).
--
--   Differences from the source:
--   - generalization: γ ∈ [γmin, γmax]^n with 0 < γmin → any γ with γ_i > 0 for every i; reason: every γ in the box has positive entries, so the Lean statement specializes to the page's
--   - reading: N = {1, …, n}, a set of n service providers → 0 < n; reason: with no provider the program (14) is infeasible (its normalization reads 0 = 1), so its value is not defined; the page's LP statements presuppose n ≥ 1
--   - encoding: f(γ) is the optimal value of problem (16) → dualValue γ, the infimum of s over the feasible (s, λ) of (15); reason: (16) is (15) with s eliminated (p. 38: 'Problem (15) in turn can be rewritten as'); dividing the first two families of constraints of (15) by γ_i, γ_k > 0 gives the max in (16), so the values coincide
--   - reading: 'strong duality must hold' → weak duality, attainment in both programs, and equality of the optimal values; reason: this is the content of LP strong duality for a feasible, bounded program; each part is needed for f(γ) to be the value of (14)
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 38, proof of Theorem 1, (14), (15) and (16)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem strong_duality {n : ℕ} (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    (∀ (x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (s : ℝ) (lam : Fin n → Fin n → ℝ),
      PrimalFeasible γ x y w → DualFeasible γ s lam → primalObj γ x y w ≤ s) ∧
    (∃ x y : Fin n → ℝ, ∃ w : Fin n → Fin n → ℝ,
      PrimalFeasible γ x y w ∧ primalObj γ x y w = lpValue γ) ∧
    (∃ lam : Fin n → Fin n → ℝ, DualFeasible γ (dualValue γ) lam) ∧
    lpValue γ = dualValue γ := by sorry

end ProviderGuarantee.Bound
