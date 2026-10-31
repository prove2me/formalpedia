-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_10_ii
-- name    : QKPSDP.lemma_4_10_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:43.201986+00:00
-- url     : https://prove2.me/theorems/f14ec313-7de9-49a4-959b-712015473121
-- title:
--   Lemma 4.10(ii) — if $C \in \mathcal Q(G)$ and $r \ge n + 4 - \operatorname{mr}(G)$, then $\operatorname{rank}(R) \le r - 2$
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1 and $r \ge 3$. Let $G$ be a simple graph on $[n]$, $C \in \mathcal Q(G)$, and
--
--   $$
--   r \ge n + 4 - \operatorname{mr}(G).
--   $$
--
--   Then every regular first-order stationary point $R$ of (SQKELR) satisfies $\operatorname{rank}(R) \le r - 2$.
--
--   When $C$ is sparse with a pattern of large minimum rank, a small factorization rank $r$ already forces rank deficiency.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - encoding: C ∈ Q(G) for some graph G and r ≥ n + 4 − mr(G) → for every G : SimpleGraph (Fin n) with C ∈ QG G and n + 4 ≤ r + mr G; reason: "if ∃ G with P(G) then Q" is "∀ G, P(G) → Q"; r ≥ n + 4 − mr(G) and n + 4 ≤ r + mr(G) agree over ℤ; mr is the minimum (attained) written as sInf
--   - encoding: rank(R) ≤ r − 2 → R.rank + 2 ≤ r; reason: identical for r ≥ 2; avoids truncated ℕ subtraction
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.10(ii), p.16

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_IsRegularFOSP
import Definitions.Def_QKPSDP_QG
import Definitions.Def_QKPSDP_mr

namespace QKPSDP

/-- **Lemma 4.10(ii)** (Tang & Toh, arXiv:2303.06599v1, p.16): "Suppose `(a, τ)` satisfies
Assumption 1, `r ≥ 3` and `R` is a regular first order stationary point of (SQKELR). The following
statements hold. … (ii) If `C ∈ Q(G)` for some graph `G` and `r ≥ n + 4 − mr(G)`, then
`rank(R) ≤ r − 2`."

**Formalization Note** `G : SimpleGraph (Fin n)`. `r ≥ n + 4 − mr(G)` is `n + 4 ≤ r + mr G`
(identical over the integers; no truncated subtraction). `rank(R) ≤ r − 2` is `R.rank + 2 ≤ r`.
`C ∈ Q(G)` includes `C ∈ Sⁿ`. -/
theorem lemma_4_10_ii {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (τ : ℝ)
    (ha : Assumption1 a τ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) (hCG : C ∈ QG G)
    (hrG : n + 4 ≤ r + mr G) (R : Matrix (Fin n) (Fin r) ℝ) (hR : IsRegularFOSP C a τ R) :
    R.rank + 2 ≤ r := by sorry

end QKPSDP
