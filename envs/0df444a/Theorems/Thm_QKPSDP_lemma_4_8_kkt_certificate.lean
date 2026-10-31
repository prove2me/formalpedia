-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_8_kkt_certificate
-- name    : QKPSDP.lemma_4_8_kkt_certificate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:17.715091+00:00
-- url     : https://prove2.me/theorems/cf657827-fd6b-4db7-bfde-a59fcebeff1b
-- title:
--   Lemma 4.8, proof, (36)–(42) — (31), (32) and (35) certify that $Y$ is optimal for (SQKE)
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $C \in \mathbb S^n$. Let $R \in \mathcal K_{n,r}$ and let $(\mu,\lambda) \in \mathbb R^n\times\mathbb R$ satisfy the KKT equation (32) and
--
--   $$
--   -2C - 2\operatorname{diag}(\mu) - 2\lambda aa^\top \in \mathbb S^n_+ . \qquad (35)
--   $$
--
--   Then $Y = (e_1\ R^\top)^\top (e_1\ R^\top) = \begin{pmatrix} 1 & (Re_1)^\top \\ Re_1 & RR^\top\end{pmatrix}$ is a global optimal solution of (SQKE).
--
--   The multipliers of (SQKELR) supply dual variables for (SQKE) whose slack matrix $S = \begin{pmatrix} -(Re_1)^\top \\ I \end{pmatrix}(-C - \operatorname{diag}(\mu) - \lambda aa^\top)(-Re_1\ \ I)$ is positive semidefinite (42) and complementary to $Y$. No regularity of $R$ is required, which is why the same step finishes both cases of Lemma 4.8.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: Y := (e₁ R⊤)⊤(e₁ R⊤) is a global optimal solution of (SQKE) → IsGlobalOptSQKE C a τ (R *ᵥ e1 r) (R * Rᵀ), i.e. the (SQKE) pair x = Re₁, X = RR⊤; reason: (e₁ R⊤)⊤(e₁ R⊤) = (1, (Re₁)⊤; Re₁, RR⊤) since e₁⊤e₁ = 1 (proved as Y_eq in the verification file)
--   - generalization: the step is carried out in Case 1 (R regular) and invoked again in Case 2 ("once (32) holds, the remaining proof will be exactly the same as in Case 1", p.16) → no regularity hypothesis on R; reason: the step uses only (31), (32) and (35), as the page says; it specializes to both of the page's uses
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.8, proof, (36)–(42), pp.14–15

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_KKT1
import Definitions.Def_QKPSDP_IsGlobalOptSQKE

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.8, proof, (36)–(42), pp.14–15: "we will move on to use
(31), (32) and (35) to prove the global optimality of `R`. Note that we only have to prove that
`Y = (e₁ R⊤)⊤(e₁ R⊤)` is a global optimal solution of (SQKE) through the KKT conditions of
(SQKE)." The dual slack `S` of (41) is `S = (−(Re₁)⊤; I)(−C − diag(μ) − λaa⊤)(−Re₁ I) ⪰ 0` (42).

If `R ∈ K_{n,r}` (31) and `(μ, λ)` satisfy (32) and (35), then `Y` is a global optimal solution
of (SQKE).

**Formalization Note** No regularity hypothesis: Case 2 of the proof (p.16, "once (32) holds,
the remaining proof will be exactly the same as in Case 1") reuses this step at non-regular
points. `Y = (e₁ R⊤)⊤(e₁ R⊤) = (1, (Re₁)⊤; Re₁, RR⊤)` (since `e₁⊤e₁ = 1`), i.e. the pair
`x = Re₁ = R *ᵥ e₁`, `X = RR⊤ = R * Rᵀ` of (SQKE). -/
theorem lemma_4_8_kkt_certificate {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ)
    (R : Matrix (Fin n) (Fin r) ℝ) (hR : R ∈ K a τ) (μ : Fin n → ℝ) (lam : ℝ)
    (h32 : KKT1 C a τ R μ lam)
    (h35 : (-(2 : ℝ) • C - (2 : ℝ) • diagonal μ - (2 * lam) • vecMulVec a a).PosSemidef) :
    IsGlobalOptSQKE C a τ (R *ᵥ e1 r) (R * Rᵀ) := by sorry

end QKPSDP
