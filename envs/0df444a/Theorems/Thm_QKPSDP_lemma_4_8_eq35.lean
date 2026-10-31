-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_8_eq35
-- name    : QKPSDP.lemma_4_8_eq35
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:12.036017+00:00
-- url     : https://prove2.me/theorems/4b9517c7-f3f2-46e0-b8c3-c8dbdf94f926
-- title:
--   Lemma 4.8, proof, (35) — $-2C - 2\operatorname{diag}(\mu) - 2\lambda aa^\top \succeq 0$ at a rank-deficient regular point
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1, $r \ge 3$ and $C \in \mathbb S^n$. Let $R \in \mathcal K_{n,r}$ be regular, let $(\mu,\lambda)$ satisfy the first-order equation (32) and the second-order condition (33) on the tangent space (34), and suppose $\operatorname{rank}(R) \le r - 2$. Then
--
--   $$
--   -2C - 2\operatorname{diag}(\mu) - 2\lambda aa^\top \in \mathbb S^n_+ . \qquad (35)
--   $$
--
--   The rank deficiency provides directions $db^\top$ in the tangent space for every $d \in \mathbb R^n$, which turns the second-order condition on the tangent space into positive semidefiniteness on all of $\mathbb R^n$. This is the dual feasibility needed for the certificate of global optimality.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - encoding: second-order condition (33) over the tangent cone T_{K_{n,r}}(R) → KKT2: (33) over the tangent space (34); reason: the page states that under LICQ the tangent cone is the tangent space (34); KKT2 is only used at regular points
--   - encoding: rank(R) ≤ r − 2 → R.rank + 2 ≤ r; reason: identical for r ≥ 2; avoids truncated ℕ subtraction
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.8, proof, Case 1, (35), p.14

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_IsRegular
import Definitions.Def_QKPSDP_KKT1
import Definitions.Def_QKPSDP_KKT2

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.8, proof, Case 1, (35), p.14: at a regular point
`R ∈ K_{n,r}` with multipliers `(μ, λ)` satisfying (32) and (33) over the tangent space (34), if
`rank(R) ≤ r − 2` then "there exists `b ∈ ℝʳ` such that `b ≠ 0`, `b₁ = 0` and `Rb = 0`. It is
easy to see that for any `d ∈ ℝⁿ`, `db⊤ ∈ T_R K_{n,r}`. Substituting `db⊤` into (33), we get that
`−2C − 2diag(μ) − 2λaa⊤ ∈ S₊ⁿ`." (35)

**Formalization Note** `rank(R) ≤ r − 2` is `R.rank + 2 ≤ r` (no truncated subtraction; the same
for `r ≥ 2`). `C ∈ Sⁿ` is `C.IsSymm`. `S₊ⁿ` is `Matrix.PosSemidef`. -/
theorem lemma_4_8_eq35 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) (hr : 3 ≤ r)
    (R : Matrix (Fin n) (Fin r) ℝ) (hR : R ∈ K a τ) (hreg : IsRegular a τ R)
    (μ : Fin n → ℝ) (lam : ℝ) (h32 : KKT1 C a τ R μ lam) (h33 : KKT2 C a τ R μ lam)
    (hrank : R.rank + 2 ≤ r) :
    (-(2 : ℝ) • C - (2 : ℝ) • diagonal μ - (2 * lam) • vecMulVec a a).PosSemidef := by sorry

end QKPSDP
