-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_10_null_set
-- name    : QKPSDP.lemma_4_10_null_set
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:33.991816+00:00
-- url     : https://prove2.me/theorems/95adaec5-9157-4796-8abe-237d729094cb
-- title:
--   Lemma 4.10, proof of (i), p.17 — the exceptional cost matrices form a null set
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1, $r \ge 3$ and $\frac{(r-2)(r-1)}{2} > n + 1$. With $\mathcal M_{\le n+2-r} := \{A \in \mathbb S^n : \operatorname{rank}(A) \le n + 2 - r\}$, the set
--
--   $$
--   \bigl\{ C \in \mathbb S^n :\ -C \in \mathcal M_{\le n+2-r} + \{\operatorname{diag}(\mu) + \lambda aa^\top : \mu \in \mathbb R^n,\ \lambda \in \mathbb R\} \bigr\}
--   $$
--
--   has Lebesgue measure zero in $\mathbb S^n \cong \mathbb R^{n(n+1)/2}$.
--
--   Its dimension is at most $\frac{n(n+1)}{2} - \frac{(r-2)(r-1)}{2} + n + 1 < \frac{n(n+1)}{2} = \dim\mathbb S^n$. This is the meaning of "generic" in Lemma 4.10(i) and Theorem 4.11.
--
--   **Formalization Note** $\mathbb S^n$ is parametrized by its upper-triangular entries; "measure zero" is Lebesgue outer measure zero, with no measurability claimed. $\operatorname{rank}(A) \le n + 2 - r$ is written $\operatorname{rank}(A) + r \le n + 2$, so that for $r > n + 2$ the set is empty, as on the page.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: (r−2)(r−1)/2 > n + 1 → 2 * (n + 1) < (r - 2) * (r - 1) in ℕ; reason: identical for r ≥ 3 (no division, no truncation)
--   - encoding: 𝕊ⁿ with Lebesgue measure; "a set of measure zero" → volume = 0 for the set of u ∈ ℝ^{n(n+1)/2} with C = symOf u in the set; reason: symOf is a linear bijection ℝ^{n(n+1)/2} → 𝕊ⁿ, so null sets correspond
--   - encoding: rank(A) ≤ n + 2 − r → rank(A) + r ≤ n + 2; reason: the same over ℤ; truncated ℕ subtraction would turn the empty case r > n + 2 into rank(A) ≤ 0
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.10, proof of (i), p.17

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_symOf

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.10, proof of (i), p.17: with
`M_{≤n+2−r} := {A ∈ Sⁿ : rank(A) ≤ n + 2 − r}`, "`−C ∈ M_{≤n+2−r} + {diag(μ) + λaa⊤ : μ ∈ ℝⁿ,
λ ∈ ℝ}` whose dimension is bounded by `n(n+1)/2 − (r−2)(r−1)/2 + n + 1 < n(n+1)/2 = dim(Sⁿ)`.
This means that `C ∈ Sⁿ` is contained in a set of measure zero."

If `(r−2)(r−1)/2 > n + 1`, the set of `C ∈ Sⁿ` with `−C − diag(μ) − λaa⊤ ∈ M_{≤n+2−r}` for some
`μ ∈ ℝⁿ`, `λ ∈ ℝ` is Lebesgue-null.

**Formalization Note** `Sⁿ` is parametrized by its upper-triangular entries `u` via `symOf`, and
"measure zero" is `volume = 0` on `ℝ^{n(n+1)/2}` (outer measure; no measurability is claimed or
needed). `(r−2)(r−1)/2 > n + 1` is `2 * (n + 1) < (r - 2) * (r - 1)` (exact for `r ≥ 3`).
`rank(A) ≤ n + 2 − r` is `rank(A) + r ≤ n + 2`, which is empty for `r > n + 2` as on the page
(truncated `ℕ` subtraction would instead give `rank(A) ≤ 0`). -/
theorem lemma_4_10_null_set {n r : ℕ} (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ)
    (hr : 3 ≤ r) (hnr : 2 * (n + 1) < (r - 2) * (r - 1)) :
    MeasureTheory.volume {u : {p : Fin n × Fin n // p.1 ≤ p.2} → ℝ |
      ∃ (μ : Fin n → ℝ) (lam : ℝ),
        (-(symOf u) - diagonal μ - lam • vecMulVec a a).rank + r ≤ n + 2} = 0 := by sorry

end QKPSDP
