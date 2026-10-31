-- Prove2me | Theorems.Thm_QKPSDP_lemma_4_10_i
-- name    : QKPSDP.lemma_4_10_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:48.713407+00:00
-- url     : https://prove2.me/theorems/08b8b4f4-c9cf-4c00-9736-541caf500080
-- title:
--   Lemma 4.10(i) — for generic $C$, regular first-order stationary points have $\operatorname{rank}(R) \le r - 2$
-- statement:
--   Suppose $(a,\tau)$ satisfies Assumption 1, $r \ge 3$ and
--
--   $$
--   \frac{(r-2)(r-1)}{2} > n + 1 .
--   $$
--
--   Then for a generic $C \in \mathbb S^n$, every regular first-order stationary point $R$ of (SQKELR) satisfies $\operatorname{rank}(R) \le r - 2$.
--
--   "Generic" means: for all $C$ outside a Lebesgue-null subset of $\mathbb S^n$, which depends on $n, r, a, \tau$ but not on $R$.
--
--   Differences from the source:
--   - encoding: Assumption 1 (p.1), in the standing setting "we consider the nontrivial case where n > 1" (p.1) → Assumption1 a τ includes 1 < n; reason: the paper's standing assumption; for n ≥ 1 it follows from Assumption 1, so it only excludes n = 0, which the paper excludes
--   - encoding: indices from 1; e₁ ∈ ℝʳ the first unit vector → Fin n, Fin r from 0; e1 r = Pi.single 0 1 with [NeZero r]; reason: e₁ needs r ≥ 1, which the hypothesis r ≥ 3 (or the page's R ∈ ℝ^{n×r} with e₁) already gives; same instances
--   - encoding: 𝕊ⁿ, 𝕊ⁿ₊, ⟨A, B⟩ = Tr(AB⊤), ‖a⊤R‖², diag(·), ∘ → Matrix (Fin n) (Fin n) ℝ with IsSymm, Matrix.PosSemidef, (A * Bᵀ).trace, (a ᵥ* R) ⬝ᵥ (a ᵥ* R), Matrix.diag / Matrix.diagonal, pointwise * on Fin n → ℝ; reason: standard Lean conventions; same instances
--   - encoding: R regular: LICQ holds at R (p.6) → IsRegular: (5) diag(μ)(2R − ee₁⊤) + λa(2a⊤R − τe₁⊤) = 0 has only the solution μ = 0, λ = 0; reason: (5) is the linear dependence relation of the n + 1 constraint gradients (p.7); same instances
--   - reading: for a generic C ∈ 𝕊ⁿ → ∀ᵐ u ∂volume on the upper-triangular coordinates u ∈ ℝ^{n(n+1)/2} of C = symOf u, chosen before R; reason: the proof of Lemma 4.10(i) (p.17) shows the exceptional C form "a set of measure zero" in 𝕊ⁿ; this is that reading, with one null set for all R
--   - encoding: (r−2)(r−1)/2 > n + 1 → 2 * (n + 1) < (r - 2) * (r - 1) in ℕ; reason: identical for r ≥ 3 (no division, no truncation)
--   - encoding: rank(R) ≤ r − 2 → R.rank + 2 ≤ r; reason: identical for r ≥ 2; avoids truncated ℕ subtraction
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.10(i), p.16

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_IsRegularFOSP
import Definitions.Def_QKPSDP_symOf

open Matrix

namespace QKPSDP

/-- **Lemma 4.10(i)** (Tang & Toh, arXiv:2303.06599v1, p.16): "Suppose `(a, τ)` satisfies
Assumption 1, `r ≥ 3` and `R` is a regular first order stationary point of (SQKELR). The following
statements hold. (i) If `(r−2)(r−1)/2 > n + 1`, then for a generic `C ∈ Sⁿ`, `rank(R) ≤ r − 2`."

**Formalization Note** "Generic `C ∈ Sⁿ`" is `∀ᵐ u ∂volume` over the upper-triangular coordinates
`u ∈ ℝ^{n(n+1)/2}` of `C = symOf u`. The exceptional null set may depend on `n, r, a, τ` but not on
`R`: the quantifiers are `∀ᵐ u, ∀ R`. `(r−2)(r−1)/2 > n + 1` is `2 * (n + 1) < (r - 2) * (r - 1)`;
`rank(R) ≤ r − 2` is `R.rank + 2 ≤ r`. -/
theorem lemma_4_10_i {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ)
    (hr : 3 ≤ r) (hnr : 2 * (n + 1) < (r - 2) * (r - 1)) :
    ∀ᵐ u : ({p : Fin n × Fin n // p.1 ≤ p.2} → ℝ), ∀ R : Matrix (Fin n) (Fin r) ℝ,
      IsRegularFOSP (symOf u) a τ R → R.rank + 2 ≤ r := by sorry

end QKPSDP
