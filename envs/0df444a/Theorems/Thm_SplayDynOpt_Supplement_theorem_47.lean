-- Prove2me | Theorems.Thm_SplayDynOpt_Supplement_theorem_47
-- name    : SplayDynOpt.Supplement.theorem_47
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:09:38.33558+00:00
-- url     : https://prove2.me/theorems/2e54428e-1223-4e28-b179-3069cdccd5b8
-- title:
--   Theorem 47 — normal form for split sequences (ribless forests of logarithmic depth, $O(n)$ steps, rotations at depth $O(1)$) (corrected: $n\ge1$)
-- statement:
--   There are constants $k\in\mathbb N$ and $C,K\in\mathbb R$ such that for every $n\ge1$ and every permutation $x_1,\dots,x_n$ of $[n]$ there are forests $\mathcal F_0,\dots,\mathcal F_\ell$ and times $1\le t_1<\dots<t_n\le\ell$ with
--   $$
--   \ell\le K\cdot n
--   $$
--   such that
--
--   1. $\mathcal F_0$ consists of a single binary search tree on $[n]$;
--   2. for every $1\le i\le\ell$, every $T\in\mathcal F_i$ is a binary search tree on a sub-interval of $[n]$ that is $k$-ribless and of depth at most $C\log_2|T|$;
--   3. $\mathcal F_\ell$ consists of $n$ one-node binary search trees;
--   4. at every step $i\in\{1,\dots,\ell\}\setminus\{t_1,\dots,t_n\}$ exactly one tree $T$ leaves the forest and exactly one tree $T'$ enters, where $T'$ is obtained from $T$ by one rotation of a key of depth at most $k$;
--   5. at time $t_j$, either the forest is unchanged and $x_j$ is already a one-node tree, or a tree $T$ with root $x_j$ is replaced by its left subtree $T_L$, the one-node tree $x_j$ and its right subtree $T_R$ (an empty $T_L$ or $T_R$ left out).
--
--   A forest schedule with these five properties is what the definition `IsSplitSchedule` of this supplement describes. The theorem says that the optimal way of performing any sequence of $n$ splits can be put in a normal form whose trees are all ribless and of logarithmic depth and whose rotations all happen near a root, with only $O(n)$ steps. It plays for the split conjecture the role Theorem 2 plays for dynamic optimality, and it is the assumption on the optimal forest that the proof of Theorem 48 needs.
--
--   **Formalization Note** The depth of a tree counts edges; in Lean the bound is $\mathrm{height}(T)\le C\log_2|T|+1$ with Mathlib's node-counting height.
--
--   Differences from the source:
--   - correction: for any permutation x₁,…,x_n of [n] (every n) → n ≥ 1; reason: false at n = 0 (the empty permutation): F₀ = {T₀} with T₀ the empty tree on [0], F_ℓ must consist of 0 trees, so ℓ ≥ 1, but with no split times every step i ≥ 1 must rotate a tree of F_{i−1}, and the empty tree admits no rotation; for n ≥ 1 nothing changes
--   - reading: ℓ = O(n), ribless, depth O(log |T|), depth at most O(1) → ∃ k C K before n and the permutation: ℓ ≤ K·n, k-ribless, depth ≤ C·log₂|T|, rotation depth ≤ k, for every n ≥ 1; reason: the constants are uniform in n and the permutation; one k serves both O(1) bounds since both properties are monotone in k; K absorbs the finitely many small n
--   - encoding: depth of T (edges) → BinaryTree.height T ≤ C·log₂|T| + 1; reason: Mathlib's height counts nodes, one more than the largest depth in edges; a singleton has depth 0
--   - encoding: forests, t₁ < ⋯ < t_n ∈ [ℓ] → Finset (BinaryTree ℕ) indexed by ℕ; times t 0 < ⋯ < t (n−1) in {1,…,ℓ}; reason: 0-based indexing of the times; same instances
--   - encoding: {T_L, T_x, T_R}, with T_L or T_R omitted when empty → {L, node x nil nil, R} filtered by ≠ nil; reason: the empty tree is nil; same instances
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 47, p.76 (App. C.6; proof pp.76–77)

import Mathlib
import Definitions.Def_SplayDynOpt_Supplement_IsSplitSchedule

set_option autoImplicit false

namespace SplayDynOpt.Supplement

/-- **Theorem 47 (normal form for split sequences; corrected: n ≥ 1).** There are constants `k`, `C` and `K` such
that for every `n ≥ 1` and every permutation `x₁, …, x_n` of `[n]` there are forests
`F 0, …, F ℓ` and times `1 ≤ t₁ < ⋯ < t_n ≤ ℓ` with `ℓ ≤ K · n` forming a normal-form forest
schedule (`IsSplitSchedule k C n xs ℓ F t`): `F 0` is a single BST on `[n]`; every tree of
`F 1, …, F ℓ` is a `k`-ribless BST on a sub-interval of `[n]` of depth at most `C · log₂ |T|`;
`F ℓ` consists of `n` singletons; every non-split step rotates one tree at depth at most `k`; and
at time `tⱼ` either nothing changes and `xⱼ` is already a singleton, or a tree rooted at `xⱼ` is
split into its nonempty root subtrees and the singleton `xⱼ`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 47,
p.76 (App. C.6).

**Formalization Note.** The `O(·)`s are uniform constants chosen before `n` and the permutation:
`ℓ = O(n)` is `ℓ ≤ K · n`, "depth O(log |T|)" is depth (edges) `≤ C · log₂ |T|`, and "ribless" and
"at most O(1)" share one constant `k`. Requiring the bound for every `n ≥ 1` rather than for large
`n` is equivalent, since `K` may absorb the finitely many small `n`. **Corrected: `n ≥ 1`.** The
printed statement is false at `n = 0`: `F 0 = {T₀}` with `T₀` the empty tree on `[0]`, `F ℓ` must
hold `0` trees, so `ℓ ≥ 1`; with no split times, step `1` must rotate a tree of `F 0`, and the empty
tree admits no rotation. -/
theorem theorem_47 :
    ∃ k : ℕ, ∃ C K : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ xs : List ℕ, xs.Perm (List.range' 1 n) →
      ∃ ℓ : ℕ, ∃ F : ℕ → Finset (BinaryTree ℕ), ∃ t : ℕ → ℕ,
        IsSplitSchedule k C n xs ℓ F t ∧ (ℓ : ℝ) ≤ K * n := by sorry

end SplayDynOpt.Supplement
