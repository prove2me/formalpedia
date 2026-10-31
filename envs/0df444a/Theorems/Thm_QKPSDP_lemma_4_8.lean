-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_8
-- name    : QKPSDP.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:15.093978+00:00
-- url     : https://prove2.me/theorems/c04debe3-259b-46e9-bf2d-8423992c85ae
-- title:
--   Lemma 4.8 — a second-order stationary point with $\operatorname{rank}(R) \le r - 2$ is globally optimal
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1, $r \ge 3$ and $C \in \mathbb S^n$. If $R \in \mathcal K_{n,r}$ is a second-order stationary point of (SQKELR) (regular, or non-regular in the sense of Definition 4.5) with
--
--   $$
--   \operatorname{rank}(R) \le r - 2,
--   $$
--
--   then $Y := (e_1\ R^\top)^\top(e_1\ R^\top)$ is a global optimal solution of (SQKE), and so $R$ is a global optimal solution of (SQKELR).
--
--   This is the rank-deficiency certificate behind the main theorem; Lemma 4.10 then supplies rank deficiency.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - encoding: second-order condition (33) over the tangent cone T_{K_{n,r}}(R) → KKT2: (33) over the tangent space (34); reason: the page states that under LICQ the tangent cone is the tangent space (34); KKT2 is only used at regular points
--   - encoding: Definition 4.5: the optimal value of the SDP (29) is nonnegative → every feasible X of (29) has ⟨2diag((Cv) ∘ d) − C, X⟩ ≥ 0; reason: an infimum is ≥ 0 iff every element is; also correct when (29) is infeasible (value +∞)
--   - encoding: Y := (e₁ R⊤)⊤(e₁ R⊤) is a global optimal solution of (SQKE) → IsGlobalOptSQKE C a τ (R *ᵥ e1 r) (R * Rᵀ), i.e. the (SQKE) pair x = Re₁, X = RR⊤; reason: (e₁ R⊤)⊤(e₁ R⊤) = (1, (Re₁)⊤; Re₁, RR⊤) since e₁⊤e₁ = 1 (proved as Y_eq in the verification file)
--   - encoding: rank(R) ≤ r − 2 → R.rank + 2 ≤ r; reason: identical for r ≥ 2; avoids truncated ℕ subtraction
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.8, p.14

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_IsSOSP
import Definitions.Def_QKPSDP_IsGlobalOptSQKE
import Definitions.Def_QKPSDP_IsGlobalOptSQKELR

open Matrix

namespace QKPSDP

/-- **Lemma 4.8** (Tang & Toh, arXiv:2303.06599v1, p.14): "Suppose `(a, τ)` satisfies Assumption 1
and `r ≥ 3`. If `R ∈ K_{n,r}` is a second order stationary point of (SQKELR) such that
`rank(R) ≤ r − 2`, then `Y := (e₁ R⊤)⊤(e₁ R⊤)` is a global optimal solution of (SQKE) and so `R`
is a global optimal solution of (SQKELR)."

**Formalization Note** "Second order stationary point" is `IsSOSP` (p.12 for regular points,
Definition 4.5 for non-regular ones; `R ∈ K_{n,r}` is part of it). `Y` is the (SQKE) pair
`x = Re₁`, `X = RR⊤`. `rank(R) ≤ r − 2` is `R.rank + 2 ≤ r`. `C ∈ Sⁿ` is `C.IsSymm`. -/
theorem lemma_4_8 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) (hr : 3 ≤ r)
    (R : Matrix (Fin n) (Fin r) ℝ) (hR : IsSOSP C a τ R) (hrank : R.rank + 2 ≤ r) :
    IsGlobalOptSQKE C a τ (R *ᵥ e1 r) (R * Rᵀ) ∧ IsGlobalOptSQKELR C a τ R := by sorry

end QKPSDP
