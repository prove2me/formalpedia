-- Prove2me | Theorems.Thm_SplayDynOpt_Supplement_theorem_48
-- name    : SplayDynOpt.Supplement.theorem_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:10:16.68378+00:00
-- url     : https://prove2.me/theorems/9503e9af-7138-4e3c-893a-e8bf7ea49dcd
-- title:
--   Theorem 48 — the split conjecture holds up to a factor $\log\log n\cdot\log^2\log\log n$
-- statement:
--   Let $L(n)=\max(1,\log_2\log_2 n)\cdot\max(1,\log_2\log_2\log_2 n)^2$. There is a constant $C$ such that for every $n$, every binary search tree $T$ on $[n]=\{1,\dots,n\}$ (a splay tree in any configuration) and every permutation $x_1,\dots,x_n$ of $[n]$, the total cost of the splitting process $\mathrm{split}(x_1),\dots,\mathrm{split}(x_n)$ of $T$ by splaying satisfies
--   $$
--   \mathrm{splitCost}(T,x_1\dots x_n)\le C\cdot n\cdot L(n).
--   $$
--   Each split splays $x_j$ to the root of the current tree containing it, at cost $1$ plus the number of rotations, and then deletes the root for free, leaving its two subtrees as independent trees.
--
--   The split conjecture of Lucas and Pettie asks for the bound $O(n)$; this theorem proves it up to the factor $\log\log n\cdot\log^2\log\log n$, the same factor as in the dynamic optimality result of Theorem 1.
--
--   **Formalization Note** All logarithms are binary. $L(n)$ is the published `SplayDynOpt.loglogFactor`; its clamps change it only for $n<16$.
--
--   Differences from the source:
--   - encoding: a splay tree over n nodes → a BST on [n] = {1,…,n}; reason: keys are only compared (§2.1, p.3), so any n-key set is order-isomorphic to [n]
--   - reading: the total cost of the splitting process of T → for every permutation x₁,…,x_n of [n], the cost of split(x₁),…,split(x_n) starting from T, each split costing 1 + #rotations of its splay, root deletions free; reason: the splitting process is defined on p.77 and the split conjecture on p.78 quantifies over every permutation; the proof on p.78 counts rotations and free root deletes; charging 1 per split adds n, inside the bound
--   - reading: O(n log log n log² log log n) → ∃ C before n, T and the permutation: splitCost ≤ C·n·loglogFactor n for every n; reason: loglogFactor n = max(1, log₂log₂n)·max(1, log₂log₂log₂n)² equals log log n·(log log log n)² for n ≥ 16 and is ≥ 1, and the cost is finite for each n < 16, so the bound for all n is equivalent to the asymptotic one (at n = 0 both sides are 0); log² log log n is read as (log log log n)², as in Theorem 1
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 48, p.78 (App. D; splitting process p.77, split conjecture p.78)

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_loglogFactor
import Definitions.Def_SplayDynOpt_Supplement_splitCost

set_option autoImplicit false

namespace SplayDynOpt.Supplement

open SplayDynOpt

/-- **Theorem 48 (the split conjecture up to `log log n · log² log log n`).** There is a constant
`C` such that for every `n`, every initial splay tree `T` (an arbitrary BST on `[n]`) and
every permutation `x₁, …, x_n` of `[n]`, the total cost of splitting `T` at `x₁, …, x_n` by
splaying is at most `C · n · L(n)`, with `L(n) = max(1, log₂log₂n) · max(1, log₂log₂log₂n)²`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 48, p.78
(App. D); the splitting process is defined on p.77 and the split conjecture on p.78.

**Formalization Note.** "Any configuration" is every BST on `[n]`; "the splitting process" splits
at every key, in the order of an arbitrary permutation (the split conjecture, p.78). Each split
costs `1 + #rotations` of its splay; deleting the root is free (p.78). `L(n)` is the published
`loglogFactor`, the clamped form of `log log n · log² log log n` (logarithms binary, footnote 6,
p.19); since it equals the unclamped factor for `n ≥ 16`, it is `≥ 1`, and the cost is finite for
each of the finitely many `n < 16`, the bound for all `n` with one `C` is equivalent to the
printed `O(n log log n log² log log n)` (at `n = 0` both sides are `0`). `C` is chosen before `n`,
`T` and the permutation. -/
theorem theorem_48 :
    ∃ C : ℝ, ∀ n : ℕ, ∀ T : BinaryTree ℕ, IsBSTOn n T →
      ∀ xs : List ℕ, xs.Perm (List.range' 1 n) →
        (splitCost T xs : ℝ) ≤ C * n * loglogFactor n := by sorry

end SplayDynOpt.Supplement
