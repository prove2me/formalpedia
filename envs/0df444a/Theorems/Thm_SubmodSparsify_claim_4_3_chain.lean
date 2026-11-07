-- Prove2me | Theorems.Thm_SubmodSparsify_claim_4_3_chain
-- name    : SubmodSparsify.claim_4_3_chain
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:19.351586+00:00
-- url     : https://prove2.me/theorems/4e84439b-b28a-4587-bae7-4b705397970e
-- title:
--   Claim 4.3, first sentence — Algorithm 2 computes the exact chain and shares with $O(|E|)$ calls to FindMinimizer
-- statement:
--   There is an absolute constant $K$ with the following property. Let $E$ be a finite ground set and $h_1, \dots, h_m : 2^E \to \mathbb R_{\ge 0}$ monotone submodular functions with $h_i(\emptyset) = 0$. For every order in which FindMinimizer loops over $E$, Algorithm 2 (Decomposition, Recover, FindMinimizer)
--
--   1. computes the exact chain $(P_0, \dots, P_L)$ of (14);
--   2. returns the component shares $(s_1, \dots, s_m)$ of (15);
--   3. makes at most $K(|E| + 1)$ calls to FindMinimizer.
--
--   Correctness rests on Lemma 4.2, Item 2: each parametric minimizer is a prefix of the chain, so Recover splits the index range of the chain at every call.
--
--   Differences from the source:
--   - encoding: h_1, …, h_m : 2^E → ℝ≥0 nonnegative monotone submodular with h_i(∅) = 0; P_0 and B_j the inclusion-wise largest zero set / minimizer → hs : Fin m → Finset α → ℝ with nonnegativity, monotonicity and submodularity hypotheses on subsets of E only; largest = union of all zero sets / minimizers (definitions of SubmodSparsify.chain); reason: Lean representation of a set function on 2^E; the union is the largest set because zero sets and minimizers are closed under union (p.19), which is not assumed
--   - generalization: FindMinimizer loops "for all v ∈ E" in an unspecified order → the claim holds for every duplicate-free list ord enumerating E; reason: the claim is true for each order and specializes to any fixed one
--   - encoding: Algorithm 2 as pseudocode; O(|E|) calls → the Lean model SubmodSparsify.decomposition (Recover with fuel |E| + 1, which exceeds the recursion depth L ≤ |E|) and calls ≤ K(|E| + 1) for one absolute K; reason: the +1 covers E = ∅, where Decomposition still makes its one call at t = 0
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Claim 4.3, p.22 (PDF p.24); Algorithm 2, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SubmodSparsify_chain
import Definitions.Def_SubmodSparsify_decomposition

namespace SubmodSparsify

/-- **Claim 4.3, first sentence** (p.22): Algorithm 2 recovers the chain and the shares with
`O(|E|)` calls to FindMinimizer.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Claim 4.3, p.22; Algorithm 2, p.22.

There is an absolute constant `K` such that for every nonnegative monotone submodular family
`h₁, …, h_m` on `E` with `hᵢ(∅) = 0` and every loop order of FindMinimizer, Decomposition
computes the exact chain `(P₀, …, P_L)` of (14), returns the shares `(s₁, …, s_m)` of (15), and
calls FindMinimizer at most `K(|E| + 1)` times.

**Formalization Note.** The ground set is a `Finset E` of an arbitrary type `α`, components are
`hs : Fin m → Finset α → ℝ`; "nonnegative, monotone, submodular" (the codomain `R≥0` of §4.1)
are hypotheses on subsets of `E` only. `chain h E j = P_j`, `chainLength h E = L`,
`tau h E (chain h E (j-1)) = τ_j`, `price = b_h`, `groundState = x*`, `share = s_i` (module
`SubmodSparsify.chain`), `lovasz E` is the Lovász extension (11), `h = sumFn hs = Σᵢ hᵢ`,
`H = Σᵢ ĥᵢ`, `E′ = E \ P₀`. `decomposition ord hs E` is the Lean model of Algorithm 2 (module
`SubmodSparsify.decomposition`), FindMinimizer looping over `E` in the order of the list `ord`.
`O(|E|)` is `≤ K(|E| + 1)` so that `E = ∅` (one call) is covered. -/
theorem claim_4_3_chain : ∃ K : ℕ, ∀ {α : Type} [DecidableEq α] {m : ℕ} (E : Finset α) (hs : Fin m → Finset α → ℝ)
      (hnn : ∀ i C, C ⊆ E → 0 ≤ hs i C)
      (hmono : ∀ i A B, A ⊆ B → B ⊆ E → hs i A ≤ hs i B)
      (hsub : ∀ i A B, A ⊆ E → B ⊆ E → hs i (A ∪ B) + hs i (A ∩ B) ≤ hs i A + hs i B)
      (h0 : ∀ i, hs i ∅ = 0)
      (ord : List α), ord.Nodup → ord.toFinset = E →
      (decomposition ord hs E).chain =
          (List.range (chainLength (sumFn hs) E + 1)).map (chain (sumFn hs) E) ∧
        (∀ i, (decomposition ord hs E).shares i = share hs E i) ∧
        (decomposition ord hs E).calls ≤ K * (E.card + 1) := by sorry

end SubmodSparsify
