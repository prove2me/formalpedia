-- Prove2me | Theorems.Thm_RegimeDRCVaR_lemma_EC2
-- name    : RegimeDRCVaR.lemma_EC2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:32.934862+00:00
-- url     : https://prove2.me/theorems/3b041afa-dcd5-4fac-9a1d-3a298b7be323
-- title:
--   Lemma EC.2 — conic strong duality under a strictly feasible point (Boyd–Vandenberghe Example 5.12)
-- statement:
--   Let $\bar K\subseteq\mathbb R^{I+1}$ be a proper cone, $G\in\mathbb R^{t\times(I+1)}$, $f\in\mathbb R^t$, and fix $x,r_{nk}\in\mathbb R^I$ and $\beta_k\in\mathbb R$. Consider the conic problem
--   $$
--   \min_{p,u}\ -x'p+\beta_ku-r_{nk}'x\quad\text{s.t.}\quad G\binom{p}{u}=f,\ \ \binom{p}{u}\in\bar K \tag{EC.4}
--   $$
--   and its dual
--   $$
--   \max_{\gamma\in\mathbb R^t}\ f'\gamma-r_{nk}'x\quad\text{s.t.}\quad\binom{-x}{\beta_k}-G'\gamma\in\bar K^*. \tag{EC.5}
--   $$
--   If some $(p;u)$ in the interior of $\bar K$ satisfies $G(p;u)=f$, then the optimal values of (EC.4) and (EC.5) are equal.
--
--   In the proof of Theorem 1 this turns each semi-infinite constraint of (EC.3) into finitely many conic constraints.
--
--   **Formalization Note** $G$ is given by its blocks, $G(p;u)=G_pp+u\,g$, so that $G'\gamma=(G_p^{\mathsf T}\gamma;\ g'\gamma)$. The optimal values are an infimum and a supremum in the extended reals (the supremum over an empty dual feasible set is $-\infty$). Attainment is not asserted.
--
--   Differences from the source:
--   - encoding: G ∈ ℝ^{t×n} acting on (p_nk; u_k) ∈ ℝ^{I+1} → G given by blocks Gp : Matrix (Fin t) (Fin I) ℝ and g : Fin t → ℝ; G′γ = (Gpᵀγ, g ⬝ γ); reason: the printed n is a typo for I + 1, the only size for which G(p;u) is defined; the block form is every such matrix
--   - reading: strong duality holds → the EReal infimum of (EC.4) over its feasible set equals the EReal supremum of (EC.5) over its feasible set; reason: equality of optimal values is the meaning of strong duality in Boyd–Vandenberghe §5.2.3; attainment is not printed and not added
--   - encoding: proper cone K̄ ⊆ ℝ^{I+1}; (p;u) ≻_K̄ 0 → IsProperCone K on (Fin I → ℝ) × ℝ; a point of interior K; reason: Lean convention: cone, convex, closed, solid, pointed, as in Boyd–Vandenberghe §2.4.1; ≻_K̄ 0 means interior
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Lemma EC.2 (Example 5.12 in Boyd and Vandenberghe (2004)), displays (EC.4)–(EC.5), pp.ec2–ec3

import Mathlib
import Definitions.Def_RegimeDRCVaR_dualCone
import Definitions.Def_RegimeDRCVaR_IsProperCone

open Matrix

namespace RegimeDRCVaR

/-- **Lemma EC.2 (Example 5.12 in Boyd and Vandenberghe (2004))** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, pp.ec2–ec3):
for the conic problem
`min_{p,u} −x′p + β_k u − r′_{nk}x` s.t. `G (p; u) = f`, `(p; u) ∈ K̄`   (EC.4)
with `K̄ ⊆ ℝ^{I+1}` a proper cone, `G ∈ ℝ^{t×(I+1)}`, `f ∈ ℝ^t`, and its dual
`max_{γ∈ℝ^t} f′γ − r′_{nk}x` s.t. `(−x; β_k) − G′γ ∈ K̄*`   (EC.5),
if some `(p; u) ≻_{K̄} 0` (an interior point of `K̄`) satisfies `G (p; u) = f`, then strong
duality holds: the two optimal values are equal.

**Formalization Note**
* `ℝ^{I+1}` is `(Fin I → ℝ) × ℝ`. The matrix `G` is given by its blocks: `G (p; u) = G_p p + u g`
  with `G_p ∈ ℝ^{t×I}` and `g ∈ ℝ^t`, so `G′γ = (G_pᵀγ; g′γ)`. The printed `G ∈ ℝ^{t×n}` is read
  as `ℝ^{t×(I+1)}`, the only size for which `G (p; u)` is defined.
* `x`, `β_k` and `r_{nk}` are arbitrary parameters (`rnk`, `βk`).
* Strong duality is the equality of the optimal values in `EReal`: the primal value is the
  infimum over the primal feasible set, the dual value the supremum over the dual feasible set
  (`⊥` when that set is empty). Attainment is not asserted, as on the page. -/
theorem lemma_EC2 {I t : ℕ} (K : Set ((Fin I → ℝ) × ℝ)) (hK : IsProperCone K)
    (Gp : Matrix (Fin t) (Fin I) ℝ) (g : Fin t → ℝ) (f : Fin t → ℝ)
    (x rnk : Fin I → ℝ) (βk : ℝ)
    (hslater : ∃ z ∈ interior K, Gp *ᵥ z.1 + z.2 • g = f) :
    (⨅ (z : (Fin I → ℝ) × ℝ) (_ : Gp *ᵥ z.1 + z.2 • g = f ∧ z ∈ K),
        ((-(x ⬝ᵥ z.1) + βk * z.2 - rnk ⬝ᵥ x : ℝ) : EReal)) =
      ⨆ (γ : Fin t → ℝ) (_ : ((-x, βk) - (Gpᵀ *ᵥ γ, g ⬝ᵥ γ)) ∈ dualCone K),
        ((f ⬝ᵥ γ - rnk ⬝ᵥ x : ℝ) : EReal) := by sorry

end RegimeDRCVaR
