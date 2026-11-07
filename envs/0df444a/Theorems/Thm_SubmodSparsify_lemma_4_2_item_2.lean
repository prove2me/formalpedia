-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_4_2_item_2
-- name    : SubmodSparsify.lemma_4_2_item_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:36.07854+00:00
-- url     : https://prove2.me/theorems/77b0ca49-4ab6-4f26-b9f4-4d55adff8d73
-- title:
--   Lemma 4.2, Item 2 — the largest minimizer of $h(C) - t|C|$ is $\{v : b_h(v) \le t\}$
-- statement:
--   Let $E$ be a finite ground set and $h_1, \dots, h_m : 2^E \to \mathbb R_{\ge 0}$ monotone submodular functions with $h_i(\emptyset) = 0$; let $h := \sum_i h_i$, $H := \sum_i \hat h_i$ (sum of Lovász extensions), and let $P_0 \subsetneq \dots \subsetneq P_L = E$, $B_j$, $\tau_j$, the prices $b_h$, the ground state $x^*$ and the shares $s_1, \dots, s_m$ be defined by (14) and (15). Write $E' := E \setminus P_0$.
--
--   For every $t \ge 0$, the minimizers of $C \mapsto h(C) - t|C|$ over $C \subseteq E$ are closed under union, and the inclusion-wise largest minimizer is the low-price prefix
--
--   $$P_h(t) := \arg\min_{C \subseteq E}\{h(C) - t|C|\} = \{v \in E : b_h(v) \le t\}. \qquad (17)$$
--
--   So every parametric minimization of $h$ returns a prefix of the chain, which is what lets Algorithm 2 recover the chain by divide and conquer.
--
--   Differences from the source:
--   - encoding: h_1, …, h_m : 2^E → ℝ≥0 nonnegative monotone submodular with h_i(∅) = 0; P_0 and B_j the inclusion-wise largest zero set / minimizer → hs : Fin m → Finset α → ℝ with nonnegativity, monotonicity and submodularity hypotheses on subsets of E only; largest = union of all zero sets / minimizers (definitions of SubmodSparsify.chain); reason: Lean representation of a set function on 2^E; the union is the largest set because zero sets and minimizers are closed under union (p.19), which is not assumed
--   - encoding: P_h(t), the inclusion-wise largest minimizer, equals {v ∈ E : b_h(v) ≤ t} → {v ∈ E : b_h(v) ≤ t} is a minimizer and contains every minimizer; reason: this is what "the largest minimizer equals the set" means; it does not depend on an encoding of "largest"
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 4.2, Item 2, p.20 (PDF p.22), display (17)

import Mathlib
import Definitions.Def_SubmodSparsify_chain

namespace SubmodSparsify

/-- **Lemma 4.2, Item 2** (p.20): the largest parametric minimizer is the low-price prefix.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 4.2, Item 2, p.20, display (17).

For nonnegative monotone submodular `h₁, …, h_m` on `E` with `hᵢ(∅) = 0`, `h = Σᵢ hᵢ`, and every
`t ≥ 0`: the minimizers of `C ↦ h(C) − t|C|` over `C ⊆ E` are closed under union, and the
inclusion-wise largest minimizer is `P_h(t) = {v ∈ E : b_h(v) ≤ t}` (it is a minimizer and
contains every minimizer).

**Formalization Note.** The ground set is a `Finset E` of an arbitrary type `α`, components are
`hs : Fin m → Finset α → ℝ`; "nonnegative, monotone, submodular" (the codomain `R≥0` of §4.1)
are hypotheses on subsets of `E` only. `chain h E j = P_j`, `chainLength h E = L`,
`tau h E (chain h E (j-1)) = τ_j`, `price = b_h`, `groundState = x*`, `share = s_i` (module
`SubmodSparsify.chain`), `lovasz E` is the Lovász extension (11), `h = sumFn hs = Σᵢ hᵢ`,
`H = Σᵢ ĥᵢ`, `E′ = E \ P₀`. -/
theorem lemma_4_2_item_2 {α : Type} [DecidableEq α] {m : ℕ} (E : Finset α) (hs : Fin m → Finset α → ℝ)
    (hnn : ∀ i C, C ⊆ E → 0 ≤ hs i C)
    (hmono : ∀ i A B, A ⊆ B → B ⊆ E → hs i A ≤ hs i B)
    (hsub : ∀ i A B, A ⊆ E → B ⊆ E → hs i (A ∪ B) + hs i (A ∩ B) ≤ hs i A + hs i B)
    (h0 : ∀ i, hs i ∅ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (∀ A B, A ⊆ E → B ⊆ E →
      (∀ D, D ⊆ E → sumFn hs A - t * A.card ≤ sumFn hs D - t * D.card) →
      (∀ D, D ⊆ E → sumFn hs B - t * B.card ≤ sumFn hs D - t * D.card) →
      ∀ D, D ⊆ E → sumFn hs (A ∪ B) - t * (A ∪ B).card ≤ sumFn hs D - t * D.card) ∧
    (∀ D, D ⊆ E →
      sumFn hs (E.filter (fun v => price (sumFn hs) E v ≤ t)) -
          t * (E.filter (fun v => price (sumFn hs) E v ≤ t)).card ≤
        sumFn hs D - t * D.card) ∧
    (∀ C, C ⊆ E →
      (∀ D, D ⊆ E → sumFn hs C - t * C.card ≤ sumFn hs D - t * D.card) →
      C ⊆ E.filter (fun v => price (sumFn hs) E v ≤ t)) := by sorry

end SubmodSparsify
