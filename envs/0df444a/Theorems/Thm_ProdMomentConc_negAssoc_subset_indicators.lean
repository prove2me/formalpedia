-- Prove2me | Theorems.Thm_ProdMomentConc_negAssoc_subset_indicators
-- name    : ProdMomentConc.negAssoc_subset_indicators
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:26.672204+00:00
-- url     : https://prove2.me/theorems/01258a8a-e9b3-40e1-984e-1a9dbf0dc18a
-- title:
--   §A.2 — the indicators of a uniformly random $k$-subset are negatively associated
-- statement:
--   Let $0 \le k \le n$ and let $I$ be a uniformly random $k$-subset of $[n]$. Then the indicator variables
--
--   $$
--   \big(\mathbf 1_{i \in I}\big)_{i \in [n]}
--   $$
--
--   are negatively associated in the sense of Definition 2.10.
--
--   This is the classical negative association of sampling without replacement (Joag-Dev and Proschan). In the paper it is combined with the closure of negative association under monotone functions of disjoint blocks to show that the variables $Z_j = \mathbf 1[N(j) \cap I \ne \emptyset]$ are negatively associated on each stable set of the auxiliary graph, which is what Janson's bound (13) needs.
--
--   **Formalization Note** The sample space is `Finset (Fin n)` with the law `kSubsetLaw n k`; the $i$-th variable is $1$ if $i \in I$ and $0$ otherwise. Negative association is `IsNegAssoc`.
--
--   Differences from the source:
--   - generalization: k a positive integer (the subset size of Theorem 3.5) → every 0 ≤ k ≤ n; reason: the positive k are instances
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §A.2, p.36 (PDF p.36), citing [JP83]; Definition 2.10, p.11

import Mathlib
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_IsNegAssoc

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **The indicators of a uniformly random `k`-subset are negatively associated** (§A.2, [JP83]).
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), §A.2, p.36: "the indicators (1_{i∈I})_{i∈[n]} are negatively associated, since I is sampled
without replacement [JP83]".

For `I` a uniformly random `k`-subset of `[n]` (`k ≤ n`), the family `(1[i ∈ I])_{i ∈ [n]}` is
negatively associated in the sense of Definition 2.10 (`IsNegAssoc`).

**Formalization Note.** The sample space is `Finset (Fin n)` with the law `kSubsetLaw n k`; the
`i`-th variable is `1` if `i ∈ I` and `0` otherwise. -/
theorem negAssoc_subset_indicators (n k : ℕ) (hkn : k ≤ n) :
    IsNegAssoc (fun (i : Fin n) (S : Finset (Fin n)) => if i ∈ S then (1 : ℝ) else 0)
      (kSubsetLaw n k) := by sorry

end ProdMomentConc
