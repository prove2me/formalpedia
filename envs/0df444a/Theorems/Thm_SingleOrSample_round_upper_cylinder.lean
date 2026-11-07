-- Prove2me | Theorems.Thm_SingleOrSample_round_upper_cylinder
-- name    : SingleOrSample.round_upper_cylinder
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:32.128252+00:00
-- url     : https://prove2.me/theorems/539c55f5-2e4b-4a26-9364-b7623c81a9e1
-- title:
--   Proof of Lemma 4.4 — a sampling round has upper-cylinder domination
-- statement:
--   Let a legal strategy for $n$ agents and parameter $k>0$ sample at a history with $t<n$. For every fixed set $T$ of goods, the allocation $A$ of the round satisfies
--   $$\Pr[T\subseteq A]\le\Bigl(\frac1{k(n-t)}\Bigr)^{|T|}.$$
--   The buckets may depend on the picks made so far. The final incomplete bucket stays unallocated, which preserves the bound.
--
--   Differences from the source:
--   - generalization: the bound on subsets of the ground set R_{j+1} → every set T of goods; reason: for T ⊄ R the probability is 0; the case T ⊆ R is the page's
--   - encoding: the parameter k of Algorithm 2 with p = 1/(kN_j) → 0 < k; reason: nondegeneracy, p is undefined and buckets are empty at k = 0
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), proof of Lemma 4.4, p.16

import Mathlib
import Definitions.Def_SingleOrSample_runLaw

namespace SingleOrSample

/-- **A sampling round has upper-cylinder domination** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), proof of Lemma 4.4, p.16). For a legal
strategy that samples at a history with `t < n`, every fixed set `T` of goods is contained in the round's
allocation with probability at most `(1/(k(n − t)))^|T|`.

**Formalization Note.** Every `T`, not only `T ⊆ R`; for a `T` outside `R` the probability is `0`. -/
theorem round_upper_cylinder {m n k : ℕ} (hk : 0 < k) (σ : Strategy m) (hσ : Legal n k σ) (h : Hist m)
    (ht : specialCount h < n) (hc : σ.choose h = none) (T : Finset (Fin m)) :
    (roundLaw n k σ h).toOuterMeasure {r | T ⊆ r.goods} ≤
      ENNReal.ofReal ((1 / ((k : ℝ) * ((n - specialCount h : ℕ) : ℝ))) ^ T.card) := by sorry

end SingleOrSample
