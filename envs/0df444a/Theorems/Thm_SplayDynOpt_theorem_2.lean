-- Prove2me | Theorems.Thm_SplayDynOpt_theorem_2
-- name    : SplayDynOpt.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:25.411025+00:00
-- url     : https://prove2.me/theorems/d3a513a9-7dde-43c2-989d-4c8ebefb246d
-- title:
--   Theorem 2 — normal form for the optimal tree (corrected: $n\ge2$)
-- statement:
--   There are constants $k,C\in\mathbb N$ and $K\in\mathbb R$ such that for every $n\ge2$ and every access sequence $X=x_1,\dots,x_m$ over $[n]$ there are trees $T_0,\dots,T_\ell$ and times $1\le t_1<\dots<t_m\le\ell$ with
--   $$
--   \ell\le K\cdot\mathrm{OPT}(n,X),
--   $$
--   such that:
--
--   1. every $T_i$, $0\le i\le\ell$, is a binary search tree on $[n]$ that is $k$-ribless of height at most $C\log_2 n$;
--   2. every $T_i$, $1\le i\le\ell$, is obtained from $T_{i-1}$ by one rotation of a key of depth at most $k$;
--   3. $T_{t_j}$ has root $x_j$ for every $j$.
--
--   So the optimal tree can be replaced by one that is ribless, of logarithmic depth and rotates only near its root, at the price of a constant factor. This normal form is the tree against which the splay tree is charged.
--
--   Differences from the source:
--   - correction: for any access sequence from U = [n], t₁ < ⋯ < t_m ∈ [ℓ], for every n → for n ≥ 2; reason: false at n = 1, X = (1): t₁ ∈ {1,…,ℓ} forces ℓ ≥ 1, but a one-node tree admits no rotation (proved as theorem_2_false_at_one in the verification file); Theorem 1 is unaffected
--   - generalization: clause 1 for i ∈ [ℓ] = {1,…,ℓ} → clause 1 for i ∈ {0,…,ℓ}; reason: the proof of Theorem 1 uses T* at all times (p.14), and T₀ is one rotation at constant depth from T₁; it specializes to the printed clause
--   - reading: ribless, depth O(log n), depth at most O(1), ℓ = O(cost(T^OPT_X)) → ∃ k C K before n and X: k-ribless, height ≤ C·log₂ n, rotation depth ≤ k, ℓ ≤ K·OPT; reason: the constants are uniform in n and X, with one k serving both O(1) bounds since both are existential
--   - encoding: depth of a tree → BinaryTree.height, the largest depth plus one; reason: Mathlib convention; the same O(log n) for n ≥ 2
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 2, pp.14–15 (restated p.60, proved pp.74–75)

import Mathlib
import Definitions.Def_SplayDynOpt_IsNormalSchedule

set_option autoImplicit false

namespace SplayDynOpt

/-- **Theorem 2 (normal form for the optimal tree; corrected: n ≥ 2).** There are constants
`k, C` and `K` such that for every `n ≥ 2` and every access sequence `X = x₁, …, x_m` over
`[n]` there are trees `T₀, …, T_ℓ` and times `1 ≤ t₁ < ⋯ < t_m ≤ ℓ` with `ℓ ≤ K · OPT(n, X)`,
such that every `Tᵢ` (`0 ≤ i ≤ ℓ`) is a `k`-ribless BST on `[n]` of height at most
`C · log₂ n`, every `Tᵢ` (`1 ≤ i ≤ ℓ`) is obtained from `Tᵢ₋₁` by one rotation of a key of depth
at most `k`, and `T_{tⱼ}` has root `xⱼ`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 2, pp.14–15 (restated p.60, proved pp.74–75).

**Formalization Note.** Printed for all `n`; false at `n = 1`, `X = (1)`: `t₁ ∈ [ℓ]` forces
`ℓ ≥ 1`, but a one-node tree admits no rotation. Clause 1 is also required at `i = 0` (the
paper's `[ℓ]` starts at 1); the proof of Theorem 1 uses `T*` "at all times" (p.14). The
non-decreasing times of `IsNormalSchedule` are strengthened here to strictly increasing times in
`{1, …, ℓ}`, as printed. "Ribless" is `k`-ribless and "at most O(1)" is depth `≤ k` with one
constant `k` for both; "depth O(log n)" is `height ≤ C·log₂ n`. -/
theorem theorem_2 :
    ∃ k C : ℕ, ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ X : List ℕ, (∀ x ∈ X, x ∈ Finset.Icc 1 n) →
      ∃ E : Execution, IsNormalSchedule k C n X E ∧
        (∀ j < X.length, 1 ≤ E.time j) ∧
        (∀ j j', j < j' → j' < X.length → E.time j < E.time j') ∧
        (E.len : ℝ) ≤ K * (OPT n X : ℝ) := by sorry

end SplayDynOpt
