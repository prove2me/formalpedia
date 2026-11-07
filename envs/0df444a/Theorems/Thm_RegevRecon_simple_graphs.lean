-- Prove2me | Theorems.Thm_RegevRecon_simple_graphs
-- name    : RegevRecon.simple_graphs
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:02.864027+00:00
-- url     : https://prove2.me/theorems/ffc9e803-d987-4a52-b61f-9231def5df02
-- title:
--   Proof of Proposition 2 — simple graphs in the matching ensemble
-- statement:
--   Fix $3\le k<D$. (a) Each labeled simple $(k,D)$-regular bipartite graph arises from exactly $(k!)^m(D!)^n$ matchings, so conditioning on the event $A$ of no parallel edges gives the uniform graph of Definition 2. (b) $\liminf_{m\to\infty}\Pr(A)>0$ [Jan13, Theorem 5.1]. Together these transfer the decoder's guarantee from the matching ensemble to the ensemble of Definition 2.
--
--   Differences from the source:
--   - encoding: lim inf_{m→∞} Pr(A) > 0 → ∃ c > 0, ∃ N, Pr(A) ≥ c for all admissible n ≥ N; reason: the definition of a positive lim inf along the admissible n
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Proposition 2, p.16

import Mathlib
import Definitions.Def_RegevRecon_ConfigurationModel
import Definitions.Def_RegevRecon_Ensemble

namespace RegevRecon

open Classical in
/-- **Simple graphs in the matching ensemble**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.16: "Each labeled simple (k, D)-regular bipartite graph arises
from exactly (k!)^m(D!)^n matchings", and "For fixed k, D, lim inf_{m→∞} Pr(A) > 0 [Jan13, Theorem 5.1]", where
`A` is the event that the matched graph has no parallel edges.

**Formalization Note** `lim inf > 0` along `m k = n D` is: a positive constant bounds `Pr(A)` from below for all
large admissible `n`. -/
theorem simple_graphs {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D) :
    (∀ m n : ℕ, m * k = n * D → ∀ Bbar ∈ biregular k D m n,
      (Finset.univ.filter fun σ : Matching m k n D => NoParallelEdges σ ∧ graphOf σ = Bbar).card =
        (k.factorial) ^ m * (D.factorial) ^ n) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ∣ n * D →
      c ≤ matchingProb (m := n * D / k) (k := k) (n := n) (D := D) NoParallelEdges := by sorry

end RegevRecon
