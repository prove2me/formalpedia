-- Prove2me | Theorems.Thm_QKPSDP_kkt_solution_29
-- name    : QKPSDP.kkt_solution_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:06.051588+00:00
-- url     : https://prove2.me/theorems/1189de1e-d06c-417b-8947-e47a91784399
-- title:
--   p.13 and (43)–(45) — the SDP (29) has a KKT solution $(X, \alpha, \gamma)$
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $C \in \mathbb S^n$. Let $R = ve_1^\top \in \mathcal N_{n,r}$ with $v \in \{0,1\}^n$. Then there exist $X \in \mathbb S^n$ and $\alpha,\gamma \in \mathbb R$ with
--
--   $$
--   \bigl\langle aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d), X\bigr\rangle = 0,\quad \operatorname{Tr}(X) = 1,\quad X \in \mathbb S^n_+, \qquad (43)
--   $$
--
--   $$
--   2\operatorname{diag}((Cv)\circ d) - C - \alpha\bigl(aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d)\bigr) - \gamma I \in \mathbb S^n_+, \qquad (44)
--   $$
--
--   $$
--   \bigl\langle 2\operatorname{diag}((Cv)\circ d) - C - \alpha\bigl(aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d)\bigr) - \gamma I,\ X\bigr\rangle = 0. \qquad (45)
--   $$
--
--   The paper obtains it from Lemma A.2 and SDP strong duality with attainment (the mission's reference item `VBSDP.Duality.theorem_3_1`). It supplies the multiplier $\alpha$ used at non-regular points.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R = ve₁⊤ ∈ N_{n,r}, v ∈ {0,1}ⁿ, d = 2v − e, σ_v (pp.8, 13) → v : Fin n → ℝ with ∀ i, v i = 0 ∨ v i = 1 and vecMulVec v (e1 r) ∈ N a τ; dvec v, sigmaV v; reason: same objects; r enters only through e₁
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, p.13 ("there exists a KKT solution of (29)") and (43)–(45), p.15

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_N
import Definitions.Def_QKPSDP_obj29
import Definitions.Def_QKPSDP_IsFeasible29

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, p.13 ("We show in Lemma A.2 that the duality gap between (29)
and (30) is zero and the optimal values of both (29) and (30) are attainable, i.e., there exists a
KKT solution of (29).") with (43)–(45), p.15: for `R = ve₁⊤ ∈ N_{n,r}` there is `(X, α, γ)` with
`⟨aa⊤ − σ_vτ·diag(a ∘ d), X⟩ = 0, Tr(X) = 1, X ∈ S₊ⁿ` (43),
`2diag((Cv) ∘ d) − C − α(aa⊤ − σ_vτ·diag(a ∘ d)) − γI ∈ S₊ⁿ` (44),
`⟨2diag((Cv) ∘ d) − C − α(aa⊤ − σ_vτ·diag(a ∘ d)) − γI, X⟩ = 0` (45).

**Formalization Note** `C ∈ Sⁿ` is `C.IsSymm`; `⟨A, X⟩ = Tr(AX⊤)`. The page derives this from
Lemma A.2 and SDP strong duality with attainment (the mission's reference item
`VBSDP.Duality.theorem_3_1`). -/
theorem kkt_solution_29 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) (v : Fin n → ℝ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hN : vecMulVec v (e1 r) ∈ N a τ) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (α γ : ℝ),
      IsFeasible29 a τ v X ∧
      (obj29 C v - α • con29 a τ v - γ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((obj29 C v - α • con29 a τ v - γ • (1 : Matrix (Fin n) (Fin n) ℝ)) * Xᵀ).trace = 0 := by sorry

end QKPSDP
