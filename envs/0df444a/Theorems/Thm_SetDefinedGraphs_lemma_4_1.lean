-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_1
-- name    : SetDefinedGraphs.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:30.867762+00:00
-- url     : https://prove2.me/theorems/9933094f-a0fc-4427-8758-aaa531324a50
-- title:
--   Lemma 4.1 — a full non-$P$-compatible clause is false on $P$-homogeneous pairs
-- statement:
--   Let $P$ be a partition of $[d]$, let $C$ be a full clause over $q_{i,j}$, $i,j\in[d]$, that is not $P$-compatible, and let $u,w\in\mathbb N^d$ be $P$-homogeneous. Then $C$ evaluates to $0$ on $(u,w)$, i.e.
--   $$Q_{u,w}\ne\Delta_C .$$
--   Hence non-$P$-compatible clauses create no arcs between $P$-homogeneous vertices and can be dropped from realisations over $P$-homogeneous sets.
--
--   Differences from the source:
--
--   - encoding: a partition P of [d] → an equivalence relation P : Setoid (Fin d); reason: partitions and equivalence relations correspond bijectively
--   - encoding: C evaluates to 0 on (u, w), for a full clause C → Q_{u,w} ≠ Δ_C; reason: a full clause holds exactly on the assignment equal to its clause digraph
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.1, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.1** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.2, p.25, PDF p.27): let `C` be a full non-`P`-compatible clause, and `u, w ∈ ℕ^d` be
`P`-homogeneous. Then `C` evaluates to `0` on `(u, w)`.

**Formalization Note** A full clause is its clause digraph `C : Fin d → Fin d → Bool` and holds on `(u, w)` iff the
equality pattern `Q_{u,w}` equals it; `u` and `w` need not be distinct. A partition `P` of `[d]` is a `Setoid`. -/
theorem lemma_4_1 {d : ℕ} (P : Setoid (Fin d)) (C : FullClause (Fin d)) (hC : ¬ IsPCompatible P C)
    (u w : Fin d → ℕ) (hu : IsPHomogeneousVec P u) (hw : IsPHomogeneousVec P w) :
    eqPattern u w ≠ C := by sorry

end SetDefinedGraphs
