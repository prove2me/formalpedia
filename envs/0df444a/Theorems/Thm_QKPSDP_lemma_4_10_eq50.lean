-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_10_eq50
-- name    : QKPSDP.lemma_4_10_eq50
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:08.285894+00:00
-- url     : https://prove2.me/theorems/4c9f2419-2197-4271-90c1-4e9485323921
-- title:
--   Lemma 4.10, proof, (50) — $\operatorname{rank}(-C - \operatorname{diag}(\mu) - \lambda aa^\top) \le n + 1 - \operatorname{rank}(R)$
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1, $r \ge 3$ and $C \in \mathbb S^n$. Let $R \in \mathcal K_{n,r}$ be regular and let $(\mu,\lambda)$ satisfy the KKT equation (32) at $R$. Then
--
--   $$
--   \operatorname{rank}\bigl(-C - \operatorname{diag}(\mu) - \lambda aa^\top\bigr) \le n + 1 - \operatorname{rank}(R). \qquad (50)
--   $$
--
--   This follows from (36), a rearrangement of (32) as a product equal to zero, and Sylvester's rank inequality. It converts a large rank of $R$ into a small rank of a matrix built from $C$.
--
--   **Formalization Note** The inequality is stated as $\operatorname{rank}(-C - \operatorname{diag}(\mu) - \lambda aa^\top) + \operatorname{rank}(R) \le n + 1$.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - encoding: rank(−C − diag(μ) − λaa⊤) ≤ n + 1 − rank(R) → rank(−C − diag(μ) − λaa⊤) + rank(R) ≤ n + 1; reason: the same inequality over ℤ; avoids truncated ℕ subtraction
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.10, proof, (50), p.16

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_IsRegular
import Definitions.Def_QKPSDP_KKT1

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.10, proof, (50), p.16: "Because `R` is a regular first
order stationary point of (SQKELR), we have that the KKT condition (32) and its variant (36) hold
at `R`. After applying Sylvester's rank inequality (see 10.5 of [30]) to (36), we have that
`rank(−C − diag(μ) − λaa⊤) ≤ n + 1 − rank(R)`." (50)

**Formalization Note** (50) is stated with the sum on the left,
`rank(−C − diag(μ) − λaa⊤) + rank(R) ≤ n + 1`, which is the same inequality over the integers and
avoids truncated subtraction. `(μ, λ)` are the multipliers in (32) at `R`. -/
theorem lemma_4_10_eq50 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) (hr : 3 ≤ r)
    (R : Matrix (Fin n) (Fin r) ℝ) (hR : R ∈ K a τ) (hreg : IsRegular a τ R)
    (μ : Fin n → ℝ) (lam : ℝ) (h32 : KKT1 C a τ R μ lam) :
    (-C - diagonal μ - lam • vecMulVec a a).rank + R.rank ≤ n + 1 := by sorry

end QKPSDP
