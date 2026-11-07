-- Prove2me | Theorems.Thm_SplayDynOpt_lemma_35
-- name    : SplayDynOpt.lemma_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:45.680704+00:00
-- url     : https://prove2.me/theorems/98de62a3-2642-4439-bf99-549e04c15580
-- title:
--   Lemma 35 — the total number of zig-zigs
-- statement:
--   For all normal-form constants $k,C$ there is a constant $K$ such that for every $n$, every access sequence $X$ over $[n]$, every initial tree $S_0$ that is a binary search tree on $[n]$, and every normal-form schedule $T^*$ for $X$ with parameters $k,C$ and $\ell$ rotations, the number of zig-zigs performed by the splay tree on $X$ from $S_0$ satisfies
--   $$
--   \operatorname{zigzigCount}(S_0,X)\le K\,\bigl(n+\operatorname{cost}(T^*)\bigr)\,L(n),
--   $$
--   where $\operatorname{cost}(T^*)=m+\ell$ and $L(n)=\max(1,\log_2\log_2 n)\cdot\max(1,\log_2\log_2\log_2 n)^2$.
--
--   This is the main technical estimate of the paper, obtained by combining lazy intervals with the pairing-heap interface.
--
--   Differences from the source:
--   - generalization: T*, the tree of Theorem 2 → every normal-form schedule with parameters k, C, with non-decreasing access times and T₀ included, and K depending on k, C only; reason: the schedule of Theorem 2 is one such schedule, so this specializes to the printed statement
--   - reading: O((n + cost(T*)) · log log n · log² log log n) → K · (n + m + ℓ) · L(n), with L(n) the clamped factor; reason: for n ≥ 16 the clamps are inactive; for smaller n the zig-zig count is at most m·n, so the two forms are equivalent; cost(T*) = m + ℓ since T* pays 1 per access (p.37)
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 35, p.47 (proof pp.47–48)

import Mathlib
import Definitions.Def_SplayDynOpt_splayCost
import Definitions.Def_SplayDynOpt_IsNormalSchedule
import Definitions.Def_SplayDynOpt_loglogFactor

set_option autoImplicit false

namespace SplayDynOpt

/-- **Lemma 35.** For all normal-form constants `k, C` there is `K` such that for every `n`, every
access sequence `X` over `[n]`, every initial splay tree `S₀` (a BST on `[n]`) and every
normal-form schedule `T*` for `X` with parameters `k, C` and `ℓ` rotations, the total number of
zig-zigs performed by the splay tree on `X` from `S₀` is at most
`K · (n + cost(T*)) · L(n)`, where `cost(T*) = m + ℓ` and
`L(n) = max(1, log₂log₂n) · max(1, log₂log₂log₂n)²`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Lemma 35, p.47 (proof pp.47–48).

**Formalization Note.** `T*` is any schedule with the properties of §5.1 (`IsNormalSchedule`:
`k`-ribless, height `≤ C·log₂ n`, rotations at depth `≤ k`, non-decreasing access times, `T₀`
included); the schedule of Theorem 2 is one. `K` depends on `k, C` only. For `n ≤ 1` the statement
holds trivially: no schedule exists at `n = 1` (`height ≤ C·log₂ 1 = 0` fails) and the count is `0`. The clamps in `L(n)` only
avoid junk values of `Real.logb` for `n < 16`. -/
theorem lemma_35 :
    ∀ k C : ℕ, ∃ K : ℝ, ∀ n : ℕ, ∀ X : List ℕ, (∀ x ∈ X, x ∈ Finset.Icc 1 n) →
      ∀ S₀ : BinaryTree ℕ, IsBSTOn n S₀ → ∀ E : Execution, IsNormalSchedule k C n X E →
        (zigzigCount S₀ X : ℝ) ≤ K * ((n : ℝ) + (X.length + E.len)) * loglogFactor n := by sorry

end SplayDynOpt
