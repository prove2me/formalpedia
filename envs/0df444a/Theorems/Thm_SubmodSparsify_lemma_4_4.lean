-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_4_4
-- name    : SubmodSparsify.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:30.858067+00:00
-- url     : https://prove2.me/theorems/25f5b669-4b41-4e90-a1a9-1c7f3af12a46
-- title:
--   Lemma 4.4 — prices are monotone under marginal dominance: $b_h \le b_g$ on $E_0$
-- statement:
--   Let $E_0 \subseteq E$ be finite sets, and let $h : 2^E \to \mathbb R_{\ge 0}$ and $g : 2^{E_0} \to \mathbb R_{\ge 0}$ be monotone submodular with $h(\emptyset) = g(\emptyset) = 0$. Suppose $h$ is marginally dominated by $g$ on $E_0$:
--
--   $$h(B) - h(A) \le g(B) - g(A) \quad \text{for all } A \subseteq B \subseteq E_0. \qquad (21)$$
--
--   Then the coordinate price vectors (15) of the decompositions of $h$ on $E$ and of $g$ on $E_0$ satisfy
--
--   $$b_h(v) \le b_g(v) \quad \text{for all } v \in E_0. \qquad (22)$$
--
--   This comparison is what bounds the total influence budget in Claim 4.6.
--
--   Differences from the source:
--   - encoding: h : 2^E → ℝ≥0 and g : 2^{E₀} → ℝ≥0 monotone submodular → h g : Finset α → ℝ with nonnegativity, monotonicity and submodularity hypotheses on subsets of E (for h) and of E₀ (for g) only; reason: Lean representation of set functions on 2^E and 2^{E₀}; values of g outside 2^{E₀} are never read
--   - encoding: b_h, b_g → price h E and price g E₀ (the one-function family); reason: (15) depends on the family only through its sum
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 4.4, p.23 (PDF p.25), displays (21)–(22)

import Mathlib
import Definitions.Def_SubmodSparsify_chain

namespace SubmodSparsify

/-- **Lemma 4.4** (p.23): prices are monotone under marginal dominance.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 4.4, p.23, displays (21)–(22).

Let `E₀ ⊆ E`, and let `h : 2^E → R≥0` and `g : 2^{E₀} → R≥0` be monotone submodular with
`h(∅) = g(∅) = 0`. If `h(B) − h(A) ≤ g(B) − g(A)` for all `A ⊆ B ⊆ E₀` (21), then
`b_h(v) ≤ b_g(v)` for all `v ∈ E₀` (22), where `b_h` is the price vector of the decomposition of
`h` on `E` and `b_g` that of `g` on `E₀`.

**Formalization Note.** Set functions are `Finset α → ℝ`; the hypotheses on `h` concern subsets of
`E`, those on `g` subsets of `E₀` only (`g` is a function on `2^{E₀}`; its values elsewhere are
never read). `price h E` is `b_h` of (15) for the one-function family `h`. -/
theorem lemma_4_4 {α : Type} [DecidableEq α] (E E₀ : Finset α) (hE₀ : E₀ ⊆ E)
    (h g : Finset α → ℝ)
    (hnn : ∀ C, C ⊆ E → 0 ≤ h C) (hmono : ∀ A B, A ⊆ B → B ⊆ E → h A ≤ h B)
    (hsub : ∀ A B, A ⊆ E → B ⊆ E → h (A ∪ B) + h (A ∩ B) ≤ h A + h B) (h0 : h ∅ = 0)
    (gnn : ∀ C, C ⊆ E₀ → 0 ≤ g C) (gmono : ∀ A B, A ⊆ B → B ⊆ E₀ → g A ≤ g B)
    (gsub : ∀ A B, A ⊆ E₀ → B ⊆ E₀ → g (A ∪ B) + g (A ∩ B) ≤ g A + g B) (g0 : g ∅ = 0)
    (hdom : ∀ A B, A ⊆ B → B ⊆ E₀ → h B - h A ≤ g B - g A) :
    ∀ v ∈ E₀, price h E v ≤ price g E₀ v := by sorry

end SubmodSparsify
