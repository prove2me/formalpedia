-- Prove2me | Theorems.Thm_QKPSDP_theorem_4_11
-- name    : QKPSDP.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:24.805997+00:00
-- url     : https://prove2.me/theorems/9db5971f-f6e4-4acc-99b7-1ce9a42874ac
-- title:
--   Theorem 4.11 — under either rank condition, every second-order stationary point of (SQKELR) is globally optimal
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $r \ge 3$. Let $R$ be a second-order stationary point of (SQKELR) — regular with the first- and second-order KKT conditions, or non-regular in the sense of Definition 4.5 — and suppose at least one of the following holds:
--
--   1. $\dfrac{(r-2)(r-1)}{2} > n + 1$ and $C \in \mathbb S^n$ is generic;
--   2. $C \in \mathcal Q(G)$ for some graph $G$ and $r \ge n + 4 - \operatorname{mr}(G)$.
--
--   Then
--
--   $$
--   Y := (e_1\ R^\top)^\top (e_1\ R^\top) \ \text{is a global optimal solution of (SQKE)},
--   $$
--
--   and so $R$ is a global optimal solution of (SQKELR).
--
--   So the nonconvex factorized problem has no spurious second-order stationary points, without assuming LICQ, once $r$ is of order $\sqrt{2n}$ for generic $C$, or once $r \ge n + 4 - \operatorname{mr}(G)$ for $C$ with sparsity pattern $G$.
--
--   **Formalization Note** Condition 1: "generic" means outside a Lebesgue-null set of $\mathbb S^n$ (in upper-triangular coordinates), one null set for all $R$. Condition 2 is quantified over every graph $G$ with $C \in \mathcal Q(G)$.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - encoding: second-order condition (33) over the tangent cone T_{K_{n,r}}(R) → KKT2: (33) over the tangent space (34); reason: the page states that under LICQ the tangent cone is the tangent space (34); KKT2 is only used at regular points
--   - encoding: Definition 4.5: the optimal value of the SDP (29) is nonnegative → every feasible X of (29) has ⟨2diag((Cv) ∘ d) − C, X⟩ ≥ 0; reason: an infimum is ≥ 0 iff every element is; also correct when (29) is infeasible (value +∞)
--   - encoding: Y := (e₁ R⊤)⊤(e₁ R⊤) is a global optimal solution of (SQKE) → IsGlobalOptSQKE C a τ (R *ᵥ e1 r) (R * Rᵀ), i.e. the (SQKE) pair x = Re₁, X = RR⊤; reason: (e₁ R⊤)⊤(e₁ R⊤) = (1, (Re₁)⊤; Re₁, RR⊤) since e₁⊤e₁ = 1 (proved as Y_eq in the verification file)
--   - reading: for a generic C ∈ 𝕊ⁿ → ∀ᵐ u ∂volume on the upper-triangular coordinates u ∈ ℝ^{n(n+1)/2} of C = symOf u, chosen before R; reason: the proof of Lemma 4.10(i) (p.17) shows the exceptional C form "a set of measure zero" in 𝕊ⁿ; this is that reading, with one null set for all R
--   - encoding: (r−2)(r−1)/2 > n + 1 → 2 * (n + 1) < (r - 2) * (r - 1) in ℕ; reason: identical for r ≥ 3 (no division, no truncation)
--   - encoding: C ∈ Q(G) for some graph G and r ≥ n + 4 − mr(G) → for every G : SimpleGraph (Fin n) with C ∈ QG G and n + 4 ≤ r + mr G; reason: "if ∃ G with P(G) then Q" is "∀ G, P(G) → Q"; r ≥ n + 4 − mr(G) and n + 4 ≤ r + mr(G) agree over ℤ; mr is the minimum (attained) written as sInf
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Theorem 4.11, p.17

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_IsSOSP
import Definitions.Def_QKPSDP_IsGlobalOptSQKE
import Definitions.Def_QKPSDP_IsGlobalOptSQKELR
import Definitions.Def_QKPSDP_QG
import Definitions.Def_QKPSDP_mr
import Definitions.Def_QKPSDP_symOf

open Matrix

namespace QKPSDP

/-- **Theorem 4.11** (Tang & Toh, arXiv:2303.06599v1, p.17): "Suppose `(a, τ)` satisfies
Assumption 1 and `r ≥ 3`. If `R` is a second order stationary point of (SQKELR) and at least one
of the following two conditions are satisfied
1. `(r−2)(r−1)/2 > n + 1` and `C ∈ Sⁿ` is generic;
2. `C ∈ Q(G)` for some graph `G` and `r ≥ n + 4 − mr(G)`,
then `Y := (e₁ R⊤)⊤(e₁ R⊤)` is a global optimal solution of (SQKE) and so `R` is a global optimal
solution of (SQKELR)."

**Formalization Note** The two conditions are the two conjuncts. Condition 1: "generic `C ∈ Sⁿ`"
is `∀ᵐ u ∂volume` over the upper-triangular coordinates `u` of `C = symOf u`, with the null set
chosen before `R` (one null set for all second-order stationary points). Condition 2:
`r ≥ n + 4 − mr(G)` is `n + 4 ≤ r + mr G`. "Second order stationary point" is `IsSOSP`: regular
points with the first- and second-order KKT conditions (p.12, (32)–(34)) and non-regular points in
the sense of Definition 4.5; no LICQ is assumed. `Y` is the (SQKE) pair `x = Re₁`, `X = RR⊤`.
`[NeZero r]` follows from `r ≥ 3` and only makes `e₁` available. -/
theorem theorem_4_11 {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ)
    (hr : 3 ≤ r) :
    (2 * (n + 1) < (r - 2) * (r - 1) →
      ∀ᵐ u : ({p : Fin n × Fin n // p.1 ≤ p.2} → ℝ), ∀ R : Matrix (Fin n) (Fin r) ℝ,
        IsSOSP (symOf u) a τ R →
          IsGlobalOptSQKE (symOf u) a τ (R *ᵥ e1 r) (R * Rᵀ) ∧
            IsGlobalOptSQKELR (symOf u) a τ R) ∧
    (∀ (C : Matrix (Fin n) (Fin n) ℝ) (G : SimpleGraph (Fin n)), C ∈ QG G → n + 4 ≤ r + mr G →
      ∀ R : Matrix (Fin n) (Fin r) ℝ, IsSOSP C a τ R →
        IsGlobalOptSQKE C a τ (R *ᵥ e1 r) (R * Rᵀ) ∧ IsGlobalOptSQKELR C a τ R) := by sorry

end QKPSDP
