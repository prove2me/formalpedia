-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_4_2_item_1
-- name    : SubmodSparsify.lemma_4_2_item_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:36.081909+00:00
-- url     : https://prove2.me/theorems/1af9e88a-3958-4563-9f64-41f7ff9b9d5e
-- title:
--   Lemma 4.2, Item 1 — strictly increasing ratios, $b_h \in B(h)$, tight prefixes, $H(x^*) = \langle b_h, x^*\rangle$
-- statement:
--   Let $E$ be a finite ground set and $h_1, \dots, h_m : 2^E \to \mathbb R_{\ge 0}$ monotone submodular functions with $h_i(\emptyset) = 0$; let $h := \sum_i h_i$, $H := \sum_i \hat h_i$ (sum of Lovász extensions), and let $P_0 \subsetneq \dots \subsetneq P_L = E$, $B_j$, $\tau_j$, the prices $b_h$, the ground state $x^*$ and the shares $s_1, \dots, s_m$ be defined by (14) and (15). Write $E' := E \setminus P_0$.
--
--   If $E' \ne \emptyset$, then $0 < \tau_1 < \tau_2 < \dots < \tau_L$. Moreover $b_h$ belongs to the base polytope $B(h)$ and is tight on every prefix:
--
--   $$\sum_{v \in C} b_h(v) \le h(C) \ (\forall C \subseteq E), \qquad \sum_{v \in P_j} b_h(v) = h(P_j) \ (0 \le j \le L), \qquad H(x^*) = \langle b_h, x^* \rangle. \qquad (16)$$
--
--   The prices thus form a base of $h$ that is greedy along the chain; the identity $H(x^*) = \langle b_h, x^*\rangle$ says that $b_h$ is a subgradient of $H$ at the ground state.
--
--   Differences from the source:
--   - encoding: h_1, …, h_m : 2^E → ℝ≥0 nonnegative monotone submodular with h_i(∅) = 0; P_0 and B_j the inclusion-wise largest zero set / minimizer → hs : Fin m → Finset α → ℝ with nonnegativity, monotonicity and submodularity hypotheses on subsets of E only; largest = union of all zero sets / minimizers (definitions of SubmodSparsify.chain); reason: Lean representation of a set function on 2^E; the union is the largest set because zero sets and minimizers are closed under union (p.19), which is not assumed
--   - encoding: 0 < τ_1 < τ_2 < ⋯ < τ_L → 0 < τ_1 and τ_{j+1} < τ_{j+2} for j + 2 ≤ L, with τ_{j+1} = tau h E (chain h E j); reason: the chain of inequalities written link by link
--   - encoding: b_h ∈ B(h) and tight on every prefix → the two displayed conditions of (16) (the second at j = L gives Σ_E b_h = h(E)); reason: the paper states membership through these displays; no base-polytope definition is needed
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 4.2, Item 1, pp.19–20 (PDF pp.21–22), display (16)

import Mathlib
import Definitions.Def_SubmodSparsify_chain
import Definitions.Def_SubmodSparsify_lovasz

namespace SubmodSparsify

/-- **Lemma 4.2, Item 1** (pp.19–20): strictly increasing ratios, base polytope, tight prefixes.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 4.2, Item 1, pp.19–20, display (16).

For nonnegative monotone submodular `h₁, …, h_m` on `E` with `hᵢ(∅) = 0` and the chain, prices
and ground state of (14)–(15): if `E′ ≠ ∅` then `0 < τ₁ < τ₂ < ⋯ < τ_L`; moreover
`Σ_{v∈C} b_h(v) ≤ h(C)` for all `C ⊆ E`, `Σ_{v∈P_j} b_h(v) = h(P_j)` for `0 ≤ j ≤ L`, and
`H(x*) = ⟨b_h, x*⟩`.

**Formalization Note.** The ground set is a `Finset E` of an arbitrary type `α`, components are
`hs : Fin m → Finset α → ℝ`; "nonnegative, monotone, submodular" (the codomain `R≥0` of §4.1)
are hypotheses on subsets of `E` only. `chain h E j = P_j`, `chainLength h E = L`,
`tau h E (chain h E (j-1)) = τ_j`, `price = b_h`, `groundState = x*`, `share = s_i` (module
`SubmodSparsify.chain`), `lovasz E` is the Lovász extension (11), `h = sumFn hs = Σᵢ hᵢ`,
`H = Σᵢ ĥᵢ`, `E′ = E \ P₀`. -/
theorem lemma_4_2_item_1 {α : Type} [DecidableEq α] {m : ℕ} (E : Finset α) (hs : Fin m → Finset α → ℝ)
    (hnn : ∀ i C, C ⊆ E → 0 ≤ hs i C)
    (hmono : ∀ i A B, A ⊆ B → B ⊆ E → hs i A ≤ hs i B)
    (hsub : ∀ i A B, A ⊆ E → B ⊆ E → hs i (A ∪ B) + hs i (A ∩ B) ≤ hs i A + hs i B)
    (h0 : ∀ i, hs i ∅ = 0) :
    ((E \ chain (sumFn hs) E 0).Nonempty →
      0 < tau (sumFn hs) E (chain (sumFn hs) E 0) ∧
      ∀ j : ℕ, j + 1 < chainLength (sumFn hs) E →
        tau (sumFn hs) E (chain (sumFn hs) E j) <
          tau (sumFn hs) E (chain (sumFn hs) E (j + 1))) ∧
    (∀ C, C ⊆ E → ∑ v ∈ C, price (sumFn hs) E v ≤ sumFn hs C) ∧
    (∀ j : ℕ, j ≤ chainLength (sumFn hs) E →
      ∑ v ∈ chain (sumFn hs) E j, price (sumFn hs) E v = sumFn hs (chain (sumFn hs) E j)) ∧
    ∑ i, lovasz E (hs i) (groundState (sumFn hs) E) =
      ∑ v ∈ E, price (sumFn hs) E v * groundState (sumFn hs) E v := by sorry

end SubmodSparsify
