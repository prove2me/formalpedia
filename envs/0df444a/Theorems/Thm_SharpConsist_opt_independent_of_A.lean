-- Prove2me | Theorems.Thm_SharpConsist_opt_independent_of_A
-- name    : SharpConsist.opt_independent_of_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:36.640197+00:00
-- url     : https://prove2.me/theorems/34c95f7b-2db1-46b2-90fb-cc952ad64a1b
-- title:
--   The optimum does not depend on the hidden set (proof of Theorem 5.1)
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$ and $n=(m+1)k$. For all $k$-sets $A,A'\subseteq X$,
--   $$\mathrm{OPT}_k(f_A)=\mathrm{OPT}_k(f_{A'}),$$
--   where $\mathrm{OPT}_k$ is the maximum over subsets of $X\cup\{r\}$ of size at most $k$. The instances differ only by a permutation of the current identifiers, which fixes $r$.
--
--   Differences from the source:
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of Theorem 5.1, p.17

import Mathlib
import Definitions.Def_SharpConsist_fA
import Definitions.Def_SharpConsist_OPTk

namespace SharpConsist

/-- **The optimum does not depend on the hidden set.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent
Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.3, proof of
Theorem 5.1, p.17 ("The optimum is the same for every A because the instances differ only by a
permutation of current identifiers"). Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`.
For all `k`-sets `A, A′ ⊆ X`, `OPT_k(f_A) = OPT_k(f_{A′})`, the maximum over subsets of `X ∪ {r}` of
size at most `k`. -/
theorem opt_independent_of_A (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ)
    (hm : 32 ≤ m) (hk : 1 ≤ k) (hn : n = (m + 1) * k) (A A' : Finset (Fin n))
    (hA : A.card = k) (hA' : A'.card = k) :
    OPTk k (fA T m k A) = OPTk k (fA T m k A') := by sorry

end SharpConsist
