-- Prove2me | Theorems.Thm_QKPSDP_proposition_3_1
-- name    : QKPSDP.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:30.848509+00:00
-- url     : https://prove2.me/theorems/6b485b0b-6d50-49e8-a580-388548834a2d
-- title:
--   Proposition 3.1 — the non-regular points of $\mathcal K_{n,r}$ are exactly $\mathcal N_{n,r}$
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $r \ge 1$. Then the non-regular points of $\mathcal K_{n,r}$ are exactly
--
--   $$
--   \{ R \in \mathcal K_{n,r} : R \text{ is not regular} \} = \mathcal N_{n,r} = \{0_{n\times r}\} \sqcup \{ ve_1^\top : v \in \{0,1\}^n,\ a^\top v = \tau\}.
--   $$
--
--   So $\mathcal K_{n,r}$ fails LICQ only at finitely many points, all of rank at most one; this is what lets the paper handle non-regular points by a separate, explicit second-order condition.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Proposition 3.1, p.6 (proof p.7)

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_IsRegular
import Definitions.Def_QKPSDP_N

namespace QKPSDP

/-- **Proposition 3.1** (Tang & Toh, arXiv:2303.06599v1, p.6): "Suppose `(a, τ)` satisfy
Assumption 1. The non-regular points of `K_{n,r}` are given by
`N_{n,r} := {0_{n×r}} ⊔ { ve₁⊤ : v ∈ {0,1}ⁿ, a⊤v = τ }`." (4)

**Formalization Note** Stated as the set equality
`{R ∈ K_{n,r} : R is not regular} = N_{n,r}`, for every `r ≥ 1` (`[NeZero r]`, needed for `e₁`);
the page puts no other condition on `r`. -/
theorem proposition_3_1 {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) :
    {R : Matrix (Fin n) (Fin r) ℝ | R ∈ K a τ ∧ ¬ IsRegular a τ R} = N a τ := by sorry

end QKPSDP
