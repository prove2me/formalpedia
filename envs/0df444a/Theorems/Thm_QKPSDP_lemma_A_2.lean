-- Prove2me | Theorems.Thm_QKPSDP_lemma_A_2
-- name    : QKPSDP.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:16.144184+00:00
-- url     : https://prove2.me/theorems/fd5eda1f-4444-461f-976c-94b485a01b9e
-- title:
--   Lemma A.2 — the SDPs (29) and (30) are strictly feasible
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $C \in \mathbb S^n$. Let $R = ve_1^\top \in \mathcal N_{n,r}$ with $v \in \{0,1\}^n$, $d = 2v - e$, and $\sigma_v$ as above. Then both SDPs
--
--   $$
--   \text{(29)}\quad \min\bigl\{ \langle 2\operatorname{diag}((Cv)\circ d) - C, X\rangle : \langle aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d), X\rangle = 0,\ \operatorname{Tr}(X) = 1,\ X \in \mathbb S^n_+\bigr\},
--   $$
--
--   $$
--   \text{(30)}\quad \max\bigl\{ \beta : 2\operatorname{diag}((Cv)\circ d) - C - \alpha\bigl(aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d)\bigr) - \beta I \in \mathbb S^n_+,\ \alpha,\beta \in \mathbb R \bigr\}
--   $$
--
--   have a strictly feasible solution:
--
--   1. there is a positive definite $X$ with $\langle aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d), X\rangle = 0$ and $\operatorname{Tr}(X) = 1$;
--   2. there are $\alpha,\beta \in \mathbb R$ with $2\operatorname{diag}((Cv)\circ d) - C - \alpha(aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d)) - \beta I$ positive definite.
--
--   Strict feasibility on both sides gives zero duality gap and attainment for the pair (29)–(30).
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R = ve₁⊤ ∈ N_{n,r}, v ∈ {0,1}ⁿ, d = 2v − e, σ_v (pp.8, 13) → v : Fin n → ℝ with ∀ i, v i = 0 ∨ v i = 1 and vecMulVec v (e1 r) ∈ N a τ; dvec v, sigmaV v; reason: same objects; r enters only through e₁
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma A.2, p.32

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_N
import Definitions.Def_QKPSDP_obj29
import Definitions.Def_QKPSDP_con29

open Matrix

namespace QKPSDP

/-- **Lemma A.2** (Tang & Toh, arXiv:2303.06599v1, p.32): "Suppose `(a, τ)` satisfies
Assumption 1. Then both (29) and (30) have a strictly feasible solution."

Here (29) and (30) (p.13) are attached to `R = ve₁⊤ ∈ N_{n,r}`, `v ∈ {0,1}ⁿ`:
(29) `min { ⟨2diag((Cv) ∘ d) − C, X⟩ : ⟨aa⊤ − σ_vτ·diag(a ∘ d), X⟩ = 0, Tr(X) = 1, X ∈ S₊ⁿ }`,
(30) `max { β : 2diag((Cv) ∘ d) − C − α(aa⊤ − σ_vτ·diag(a ∘ d)) − βI ∈ S₊ⁿ, α, β ∈ ℝ }`.
Strictly feasible: for (29) some `X ≻ 0` with the two equality constraints; for (30) some
`(α, β)` with the matrix `≻ 0`.

**Formalization Note** `C ∈ Sⁿ` is `C.IsSymm`. `≻ 0` is `Matrix.PosDef`. `⟨A, X⟩ = Tr(AX⊤)`. The
`R` of the context enters only through `v`; any `r ≥ 1` is allowed. -/
theorem lemma_A_2 {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) (v : Fin n → ℝ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hN : vecMulVec v (e1 r) ∈ N a τ) :
    (∃ X : Matrix (Fin n) (Fin n) ℝ,
        X.PosDef ∧ (con29 a τ v * Xᵀ).trace = 0 ∧ X.trace = 1) ∧
      (∃ α β : ℝ, (obj29 C v - α • con29 a τ v - β • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) := by sorry

end QKPSDP
