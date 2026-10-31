-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_8_case2_multipliers
-- name    : QKPSDP.lemma_4_8_case2_multipliers
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:32.523152+00:00
-- url     : https://prove2.me/theorems/702ecd31-880c-4b50-874a-9b56a2aa6b8e
-- title:
--   Lemma 4.8, proof, Case 2, (47)–(49) — explicit multipliers at a non-regular point
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $C \in \mathbb S^n$. Let $R = ve_1^\top \in \mathcal N_{n,r}$ with $v \in \{0,1\}^n$, $d = 2v - e$, and let $\alpha \in \mathbb R$ satisfy
--
--   $$
--   2\operatorname{diag}((Cv)\circ d) - C - \alpha\bigl(aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d)\bigr) \in \mathbb S^n_+ . \qquad (47)
--   $$
--
--   Define
--
--   $$
--   \mu := -2(Cv)\circ d - \alpha\sigma_v\tau\cdot a\circ d, \qquad \lambda := \alpha. \qquad (48)
--   $$
--
--   Then $(R,\mu,\lambda)$ satisfies the first-order KKT equation (32), and $-2C - 2\operatorname{diag}(\mu) - 2\lambda aa^\top \in \mathbb S^n_+$ (35).
--
--   At a non-regular point there is no LICQ to produce multipliers; this gives them explicitly, so the certificate of Case 1 applies.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R = ve₁⊤ ∈ N_{n,r}, v ∈ {0,1}ⁿ, d = 2v − e, σ_v (pp.8, 13) → v : Fin n → ℝ with ∀ i, v i = 0 ∨ v i = 1 and vecMulVec v (e1 r) ∈ N a τ; dvec v, sigmaV v; reason: same objects; r enters only through e₁
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.8, proof, Case 2, (47)–(49), pp.15–16

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_N
import Definitions.Def_QKPSDP_KKT1
import Definitions.Def_QKPSDP_obj29
import Definitions.Def_QKPSDP_con29

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.8, proof, Case 2, (47)–(49), pp.15–16. Let
`R = ve₁⊤ ∈ N_{n,r}`, `v ∈ {0,1}ⁿ`, and suppose
`2diag((Cv) ∘ d) − C − α(aa⊤ − σ_vτ·diag(a ∘ d)) ∈ S₊ⁿ` (47). "Comparing (47) and (35), we may
choose the dual variables of (SQKELR) as follows `μ := −2(Cv) ∘ d − ασ_vτ·a ∘ d`, `λ := α`. (48)
Then from (47), (35) holds." and, by (49), (32) holds for `R`, `μ` and `λ`.

**Formalization Note** Conclusion: (32) at `(R, μ, λ)` and (35),
`−2C − 2diag(μ) − 2λaa⊤ ∈ S₊ⁿ`, with `μ, λ` substituted from (48). `∘` is `*` on vectors;
`C ∈ Sⁿ` is `C.IsSymm`. -/
theorem lemma_4_8_case2_multipliers {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) (v : Fin n → ℝ)
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hN : vecMulVec v (e1 r) ∈ N a τ) (α : ℝ)
    (h47 : (obj29 C v - α • con29 a τ v).PosSemidef) :
    KKT1 C a τ (vecMulVec v (e1 r))
        (-(2 : ℝ) • ((C *ᵥ v) * dvec v) - (α * sigmaV v * τ) • (a * dvec v)) α ∧
      (-(2 : ℝ) • C
          - (2 : ℝ) • diagonal (-(2 : ℝ) • ((C *ᵥ v) * dvec v) - (α * sigmaV v * τ) • (a * dvec v))
          - (2 * α) • vecMulVec a a).PosSemidef := by sorry

end QKPSDP
