-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_2
-- name    : SetDefinedGraphs.lemma_4_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:26:35.03612+00:00
-- url     : https://prove2.me/theorems/15713c9f-b29c-4a27-88a9-3c58231306cf
-- title:
--   Lemma 4.2 — a $P$-compatible clause is decided on the class representatives
-- statement:
--   Let $P$ be a partition of $[d]$, $I\subseteq[d]$ the set of least elements of the $P$-classes, and $C$ a full $P$-compatible clause over $q_{i,j}$, $i,j\in[d]$. If $u,w\in\mathbb N^d$ are $P$-homogeneous, then
--   $$C(u,w)=C|_I(u|_I,w|_I).$$
--   Together with Lemma 4.1 this replaces a Boolean function on $P$-homogeneous vectors by an injective DNF on the representatives (Lemma 4.3).
--
--   Differences from the source:
--
--   - encoding: equality of truth values C(u, w) = C|I(u|I, w|I) → Q_{u,w} = Δ_C ↔ Q_{u|I,w|I} = Δ_{C|I}; reason: a full clause holds iff the equality pattern equals its clause digraph
--   - encoding: a partition P of [d] → P : Setoid (Fin d); reason: partitions and equivalence relations correspond bijectively
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.2, p.26 (PDF p.28); I defined on p.26

import Mathlib
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.2** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.2, p.26, PDF p.28): let `P` be a partition of `[d]`, `I ⊆ [d]` the set of least elements of
the `P`-classes, and `C` a full `P`-compatible clause over the variables `q_{i,j}`, `i, j ∈ [d]`. If `u, w ∈ ℕ^d` are
`P`-homogeneous, then `C(u, w) = C|_I(u|_I, w|_I)`.

**Formalization Note** Both sides are truth values of full clauses: `C(u, w) = 1` iff `Q_{u,w} = Δ_C`, and
`C|_I(u|_I, w|_I) = 1` iff `Q_{u|_I, w|_I} = Δ_{C|_I}`; the equality of the two values is stated as an iff. -/
theorem lemma_4_2 {d : ℕ} (P : Setoid (Fin d)) (C : FullClause (Fin d)) (hC : IsPCompatible P C)
    (u w : Fin d → ℕ) (hu : IsPHomogeneousVec P u) (hw : IsPHomogeneousVec P w) :
    eqPattern u w = C ↔
      eqPattern (restrictVec (leastElems P) u) (restrictVec (leastElems P) w) =
        fullRestrict C (leastElems P) := by sorry

end SetDefinedGraphs
