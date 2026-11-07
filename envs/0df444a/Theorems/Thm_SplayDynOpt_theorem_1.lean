-- Prove2me | Theorems.Thm_SplayDynOpt_theorem_1
-- name    : SplayDynOpt.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:41.185953+00:00
-- url     : https://prove2.me/theorems/8e5b6081-2fc7-41e1-b1e4-38500e60c522
-- title:
--   Theorem 1 — splay trees are $O(\log\log n\cdot\log^2\log\log n)$-competitive
-- statement:
--   There is a constant $C$ such that for every $n\ge1$, every initial tree $S_0$ that is a binary search tree on $[n]$, of arbitrary shape, and every access sequence $X=x_1,\dots,x_m$ over $[n]$, of arbitrary length,
--   $$
--   \operatorname{splayCost}(S_0,X)\le C\,\bigl(\mathrm{OPT}(n,X)+n\bigr)\,L(n),
--   $$
--   where $L(n)=\max(1,\log_2\log_2 n)\cdot\max(1,\log_2\log_2\log_2 n)^2$. Here $\operatorname{splayCost}(S_0,X)$ is the cost in the root BST model of bottom-up splaying $x_1,\dots,x_m$ from $S_0$, and $\mathrm{OPT}(n,X)$ is the least cost of any dynamic binary search tree serving $X$, which knows $X$ in advance and chooses its initial tree.
--
--   This gives the first $o(\log n)$ competitive ratio for splay trees, toward the dynamic optimality conjecture of Sleator and Tarjan. The additive $n$ pays for the arbitrary initial shape.
--
--   Differences from the source:
--   - reading: cost(T, X) = O((cost(T^OPT_X, X) + n) · log log n · log² log log n) as n → ∞ → ∃ C, ∀ n ≥ 1, cost ≤ C · (OPT + n) · L(n), with L(n) clamped; reason: equivalent: for n ≥ 16 the clamps are inactive, and for smaller n a splay access costs at most n and OPT ≥ m, so cost ≤ n · OPT
--   - reading: T^OPT_X, the dynamic tree of lowest cost among all trees → OPT n X, the minimum of m + ℓ over root-model executions with free T₀, unrestricted rotations and non-decreasing access times; reason: the BST model of §2.1 (p.3) with the free initial configuration of p.4; a repeated access costs 1 as in the model
--   - encoding: a set U of n elements → keys {1,…,n}, with n ≥ 1; reason: §2.1 makes this without loss of generality since elements are only compared; at n = 0 there is no key and no access
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 1, p.13

import Mathlib
import Definitions.Def_SplayDynOpt_OPT
import Definitions.Def_SplayDynOpt_splayCost
import Definitions.Def_SplayDynOpt_loglogFactor

set_option autoImplicit false

namespace SplayDynOpt

/-- **Theorem 1 (splay trees are almost dynamically optimal).** There is a constant `C` such that
for every `n ≥ 1`, every initial splay tree `S₀` (an arbitrary BST on `[n]`) and every access
sequence `X = x₁, …, x_m` over `[n]`,
`cost(splay, X) ≤ C · (OPT(X) + n) · L(n)`, with
`L(n) = max(1, log₂log₂n) · max(1, log₂log₂log₂n)²`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 1, p.13.

**Formalization Note.** Keys are `[n] = {1, …, n}` (without loss of generality, §2.1).
`splayCost S₀ X` is the root-BST-model cost `Σⱼ (1 + #rotations)` of bottom-up splaying `x₁, …, x_m`
from `S₀`; `OPT n X` is the least cost `m + ℓ` of a root-model execution with a free initial tree.
The printed bound is `O((OPT + n) · log log n · log² log log n)` as `n → ∞`; since `L(n)` equals
`log log n · (log log log n)²` for `n ≥ 16` and `cost ≤ 2n · OPT` for every `n`, the clamped form for
all `n ≥ 1` is equivalent to it. `C` is chosen before `n`, `S₀` and `X`; `m` is arbitrary. -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ S₀ : BinaryTree ℕ, IsBSTOn n S₀ →
      ∀ X : List ℕ, (∀ x ∈ X, x ∈ Finset.Icc 1 n) →
        (splayCost S₀ X : ℝ) ≤ C * ((OPT n X : ℝ) + n) * loglogFactor n := by sorry

end SplayDynOpt
