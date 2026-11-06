-- Prove2me | Theorems.Thm_PLIAG_alpha0_bound
-- name    : PLIAG.alpha0_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:27:40.583199+00:00
-- url     : https://prove2.me/theorems/e25b4cad-608d-45a4-b9a7-1deee989fc76
-- title:
--   Proof of Theorem 4.2, p.25 — $\alpha_0\le\frac1{\ell(\tau+1)(\tau+1)L}\le\frac1{\sum_{j\in\mathcal J_k}L_j}$
-- statement:
--   Let $L_j>0$ be the constants of B1, let every block $\mathcal J_k$ be nonempty, $L=\max_{k\ge0}\sum_{j\in\mathcal J_k}L_j$, $\mu>0$, and let $\ell$ be monotonically increasing with $\ell(1)=1$. Then the step-size bound $\alpha_0$ of (4.5) satisfies
--
--   $$
--   \alpha_0\ \le\ \frac{1}{\ell(\tau+1)\cdot(\tau+1)\cdot L}\ \le\ \frac{1}{\sum_{j\in\mathcal J_k}L_j}\qquad\text{for all }k\ge0 .
--   $$
--
--   This is the first step of the proof of Theorem 4.2: it shows that every step $\alpha\le\alpha_0$ meets the step-size condition of Proposition 3.1, so the PLIAG iterates are well defined.
--
--   Differences from the source:
--   - encoding: L := max_{k≥0} Σ_{j∈J_k} L_j → Lmax Lc J := ⨆ k, Σ_{j ∈ J k} Lc j (real supremum); reason: the family takes finitely many values, so the supremum is the maximum
--   - encoding: ℓ monotonically increasing with ℓ(1) = 1 (introduced by B4 when τ > 0; ℓ(τ+1) = ℓ(1) = 1 when τ = 0) → ℓ : ℕ → ℝ with Monotone ℓ and ℓ 1 = 1 always; reason: when τ = 0 only ℓ(1) = 1 enters; ℓ(0) is never read and a monotone ℓ on the positive integers extends by ℓ(0) := ℓ(1)
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, proof of Theorem 4.2, p.25

import Mathlib
import Definitions.Def_PLIAG_Lmax
import Definitions.Def_PLIAG_alpha0

namespace PLIAG

/-- **Step-size bound in the proof of Theorem 4.2** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3,
proof of Theorem 4.2, p.25): by the definition of `L` and Bernoulli's inequality,
`α_0 ≤ 1/(ℓ(τ+1)·(τ+1)·L) ≤ 1/Σ_{j ∈ J_k} L_j` for all `k ≥ 0`.

**Formalization Note.** `L = Lmax Lc J`; the constants `L_j > 0` (B1), `J_k ≠ ∅` (step (ii)),
`μ > 0` (B3), `ℓ` monotone with `ℓ(1) = 1` (B4). Both inequalities are stated. -/
theorem alpha0_bound {N : ℕ} (Lc : Fin N → ℝ) (J : ℕ → Finset (Fin N)) (μ : ℝ) (ℓ : ℕ → ℝ)
    (τ : ℕ) (hLc : ∀ n, 0 < Lc n) (hJ : ∀ k, (J k).Nonempty) (hμ : 0 < μ)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) :
    alpha0 μ (Lmax Lc J) ℓ τ ≤ 1 / (ℓ (τ + 1) * ((τ : ℝ) + 1) * Lmax Lc J) ∧
    ∀ k : ℕ, 1 / (ℓ (τ + 1) * ((τ : ℝ) + 1) * Lmax Lc J) ≤ 1 / ∑ j ∈ J k, Lc j := by sorry

end PLIAG
