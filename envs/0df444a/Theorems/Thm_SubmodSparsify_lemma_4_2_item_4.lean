-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_4_2_item_4
-- name    : SubmodSparsify.lemma_4_2_item_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:36.08203+00:00
-- url     : https://prove2.me/theorems/545f1cbb-261e-4159-a1a5-0be83b3c1787
-- title:
--   Lemma 4.2, Item 4 — $s_i = \hat h_i(x^*)$, $\sum_i s_i = |E'| \le |E|$, $h_i(C) \le s_i \max_{v \in C} b_h(v)$
-- statement:
--   Let $E$ be a finite ground set and $h_1, \dots, h_m : 2^E \to \mathbb R_{\ge 0}$ monotone submodular functions with $h_i(\emptyset) = 0$; let $h := \sum_i h_i$, $H := \sum_i \hat h_i$ (sum of Lovász extensions), and let $P_0 \subsetneq \dots \subsetneq P_L = E$, $B_j$, $\tau_j$, the prices $b_h$, the ground state $x^*$ and the shares $s_1, \dots, s_m$ be defined by (14) and (15). Write $E' := E \setminus P_0$.
--
--   For every $i \in [m]$, the component share $s_i$ satisfies
--
--   $$s_i = \hat h_i(x^*), \qquad \sum_{i=1}^m s_i = |E'| \le |E|, \qquad h_i(C) \le s_i \cdot \max_{v \in C} b_h(v) \ (\forall C \subseteq E), \qquad (19)$$
--
--   where the maximum over the empty set is zero. The budget $\sum_i s_i \le |E|$ bounds the total sampling weight of Algorithm 1, and the low-price bound is the residual estimate behind Claim 4.5.
--
--   Differences from the source:
--   - encoding: h_1, …, h_m : 2^E → ℝ≥0 nonnegative monotone submodular with h_i(∅) = 0; P_0 and B_j the inclusion-wise largest zero set / minimizer → hs : Fin m → Finset α → ℝ with nonnegativity, monotonicity and submodularity hypotheses on subsets of E only; largest = union of all zero sets / minimizers (definitions of SubmodSparsify.chain); reason: Lean representation of a set function on 2^E; the union is the largest set because zero sets and minimizers are closed under union (p.19), which is not assumed
--   - encoding: max over the empty set defined to be zero → finMax C b (sup' on nonempty C, 0 on ∅); reason: the paper's convention, written as a definition
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 4.2, Item 4, p.20 (PDF p.22), display (19)

import Mathlib
import Definitions.Def_SubmodSparsify_chain
import Definitions.Def_SubmodSparsify_lovasz

namespace SubmodSparsify

/-- **Lemma 4.2, Item 4** (p.20): component shares, budget, and low-price bound.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 4.2, Item 4, p.20, display (19).

For nonnegative monotone submodular `h₁, …, h_m` on `E` with `hᵢ(∅) = 0` and the decomposition
(14)–(15): for every `i`, `sᵢ = ĥᵢ(x*)`; `Σᵢ sᵢ = |E′| ≤ |E|`; and
`hᵢ(C) ≤ sᵢ · max_{v∈C} b_h(v)` for all `C ⊆ E`, the maximum over the empty set being zero.

**Formalization Note.** The ground set is a `Finset E` of an arbitrary type `α`, components are
`hs : Fin m → Finset α → ℝ`; "nonnegative, monotone, submodular" (the codomain `R≥0` of §4.1)
are hypotheses on subsets of `E` only. `chain h E j = P_j`, `chainLength h E = L`,
`tau h E (chain h E (j-1)) = τ_j`, `price = b_h`, `groundState = x*`, `share = s_i` (module
`SubmodSparsify.chain`), `lovasz E` is the Lovász extension (11), `h = sumFn hs = Σᵢ hᵢ`,
`H = Σᵢ ĥᵢ`, `E′ = E \ P₀`. `finMax C b` is the maximum of `b` over `C` (zero for `C = ∅`). -/
theorem lemma_4_2_item_4 {α : Type} [DecidableEq α] {m : ℕ} (E : Finset α) (hs : Fin m → Finset α → ℝ)
    (hnn : ∀ i C, C ⊆ E → 0 ≤ hs i C)
    (hmono : ∀ i A B, A ⊆ B → B ⊆ E → hs i A ≤ hs i B)
    (hsub : ∀ i A B, A ⊆ E → B ⊆ E → hs i (A ∪ B) + hs i (A ∩ B) ≤ hs i A + hs i B)
    (h0 : ∀ i, hs i ∅ = 0) :
    (∀ i, share hs E i = lovasz E (hs i) (groundState (sumFn hs) E)) ∧
    ∑ i, share hs E i = ((E \ chain (sumFn hs) E 0).card : ℝ) ∧
    (E \ chain (sumFn hs) E 0).card ≤ E.card ∧
    (∀ i C, C ⊆ E → hs i C ≤ share hs E i * finMax C (price (sumFn hs) E)) := by sorry

end SubmodSparsify
