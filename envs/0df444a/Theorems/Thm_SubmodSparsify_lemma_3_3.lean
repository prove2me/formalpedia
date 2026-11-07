-- Prove2me | Theorems.Thm_SubmodSparsify_lemma_3_3
-- name    : SubmodSparsify.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:21.528773+00:00
-- url     : https://prove2.me/theorems/ffbb3cd4-d2a2-4d83-b1b9-e3ced06f32ba
-- title:
--   Lemma 3.3 — $f^{\to}(A,B)$ is monotone and submodular in each argument
-- statement:
--   Let $f : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular. Then the block min-cut $f^{\to}$ is monotone non-decreasing and submodular in each argument:
--
--   1. for a fixed $A$, the function $B \mapsto f^{\to}(A, B)$ on subsets $B \subseteq [n] \setminus A$ is monotone non-decreasing and submodular:
--   $$f^{\to}(A,B) \le f^{\to}(A,B') \ (B \subseteq B'), \qquad f^{\to}(A, B \cup B') + f^{\to}(A, B \cap B') \le f^{\to}(A,B) + f^{\to}(A,B');$$
--   2. for a fixed $B$, the function $A \mapsto f^{\to}(A, B)$ on subsets $A \subseteq [n] \setminus B$ is monotone non-decreasing and submodular.
--
--   Adding constraints to a minimum can only increase it; submodularity follows by combining minimizers. These properties let the paper replace the non-monotone $f_i$ by monotone submodular block min-cuts.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: B ⊆ [n] \ A (resp. A ⊆ [n] \ B) for every set involved → Disjoint A B for each argument set (for monotonicity, Disjoint A B′ for the larger set B′ ⊇ B); reason: disjointness from A is membership in [n] \ A; the smaller set inherits it
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 3.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_blockMinCut

namespace SubmodSparsify

/-- **Lemma 3.3** (p.17): the block min-cut is monotone and submodular in each argument.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 3.3, p.17.

For a nonnegative submodular `f` on `[n]` and a fixed `A`, `B ↦ f→(A, B)` is monotone
non-decreasing and submodular on subsets `B` of `[n] \ A`; for a fixed `B`, `A ↦ f→(A, B)` is
monotone non-decreasing and submodular on subsets `A` of `[n] \ B`.

**Formalization Note.** `[n]` is `Fin n`; "for `B ⊆ [n] \ A`" is `Disjoint A B` for every set
involved (for monotonicity, the larger set is disjoint from `A`, which makes the smaller one
disjoint too). -/
theorem lemma_3_3 {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : NonmonotoneSubmod.Shared.Submodular f) :
    (∀ A B B' : Finset (Fin n), Disjoint A B' → B ⊆ B' →
      blockMinCut f A B ≤ blockMinCut f A B') ∧
    (∀ A B B' : Finset (Fin n), Disjoint A B → Disjoint A B' →
      blockMinCut f A (B ∪ B') + blockMinCut f A (B ∩ B') ≤
        blockMinCut f A B + blockMinCut f A B') ∧
    (∀ B A A' : Finset (Fin n), Disjoint A' B → A ⊆ A' →
      blockMinCut f A B ≤ blockMinCut f A' B) ∧
    (∀ B A A' : Finset (Fin n), Disjoint A B → Disjoint A' B →
      blockMinCut f (A ∪ A') B + blockMinCut f (A ∩ A') B ≤
        blockMinCut f A B + blockMinCut f A' B) := by sorry

end SubmodSparsify
