-- Prove2me | Theorems.Thm_ROLDescent_eq_71
-- name    : ROLDescent.eq_71
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:45.086146+00:00
-- url     : https://prove2.me/theorems/42466cd8-ebe7-4472-aa58-e21bb34d7fe9
-- title:
--   Eq. (71) — $P_\tau(i,j)=\pi_{\tau i}(j)$ for $m_\tau\ge 3$
-- statement:
--   Let $(X, w)$ be a weighted pure complex with facet size $d$, let $\tau$ be a face with remaining rank $m_\tau \ge 3$ (that is, $|\tau| + 3 \le d$), and let $i, j \in N_\tau$ be distinct. Then
--
--   $$P_\tau(i, j) = \pi_{\tau i}(j).$$
--
--   The transition distribution from $i$ in the parent's link agrees with the outgoing distribution at the child $\tau i$. This consistency is what lets one set of facet weights serve every level of the hierarchy, and it identifies the child Gram norms inside the one-step Gram estimate.
--
--   Differences from the source:
--   - generalization: on each legal edge (τ ∪ {i, j} ∈ X) → for all distinct i, j ∈ N_τ; reason: for non-edges both sides are 0; the statement specializes to legal edges
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (71), p.30 (PDF 30)

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_ROLDescent_linkWalk

namespace ROLDescent

/-- **Eq. (71): the link walk from i is the outgoing distribution at the child τi.**
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (71), p.30 (PDF 30): "Moreover, on each legal edge, the transition
distribution from i in the parent's link agrees with the outgoing distribution at the child τi:
P_τ(i, j) = π_τi(j) (m_τ ≥ 3)."

**Formalization Note** m_τ ≥ 3 is `τ.card + 3 ≤ d`; the identity is stated for all `i, j ∈ N_τ` with
`j ≠ i` (this includes every legal edge; for a non-edge both sides are `0`). -/
theorem eq_71 {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 3 ≤ d)
    (i j : V) (hi : i ∈ HDXConc.linkVerts X τ) (hj : j ∈ HDXConc.linkVerts X τ) (hij : j ≠ i) :
    linkWalk X d w τ i j = outProb X d w (insert i τ) j := by sorry

end ROLDescent
