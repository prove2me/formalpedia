-- Prove2me | Theorems.Thm_SetDefinedGraphs_theorem_4_14
-- name    : SetDefinedGraphs.theorem_4_14
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:27:59.293798+00:00
-- url     : https://prove2.me/theorems/26c1fa72-08ed-47b7-9d69-be55b8c9718d
-- title:
--   Theorem 4.14 — injective DNFs: $(d^2\omega)^{2^{d^2}}$ parts, each a union of $2^{d^2}$ shift-colorable digraphs (corrected: $1\le d$)
-- statement:
--   Let $d\ge1$ and let $F$ be an injective DNF on $d^2$ variables. Then for every $G\in\vec{\mathcal Y}_F$ the vertex set of $G$ admits a partition into at most
--   $$(d^2\cdot\omega(G))^{2^{d^2}}$$
--   parts, each inducing a subdigraph that is a union of at most $2^{d^2}$ shift-colorable digraphs.
--
--   This is the decomposition for classes defined by injective DNFs; with Theorem 4.4 it gives Theorem 1.2.
--
--   Differences from the source:
--
--   - correction: Theorem 4.14 for every d → Theorem 4.14 under 1 ≤ d; reason: false at d = 0: ℕ^0 has one (injective) vector, whose one-vertex realisation lies in Y⃗_F with ω = 1, but (0² · 1)^{2^0} = 0 parts cannot cover a vertex
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: a partition into at most N parts → a map V → Fin N (empty parts allowed); reason: a partition into at most N possibly empty parts is a labelling by [N]
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 4.14, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Theorem 4.14** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.4, p.30, PDF p.32), corrected with `1 ≤ d`: let `F` be an injective DNF on `d²`
variables. Then, for every `G ∈ Y⃗_F`, the vertex set of `G` admits a partition into at most `(d² · ω(G))^{2^{d²}}`
parts, each inducing a subdigraph that is a union of at most `2^{d²}` shift-colorable digraphs.

**Formalization Note** The printed statement is false at `d = 0`: `ℕ^0` has one (injective) vector, its one-vertex
realisation lies in `Y⃗_F` and has `ω = 1`, but `(0 · 1)^{2^0} = 0` parts cannot cover a vertex. Hence `1 ≤ d`. A
partition into at most `N` parts is a map `V(G) → Fin N`. -/
theorem theorem_4_14 {d : ℕ} (hd : 1 ≤ d) (F : Finset (FullClause (Fin d))) (hF : IsInjectiveDNF F)
    {W : Type} (G : Digraph W) (hG : InY (dnfFun F) G) :
    ∃ part : W → Fin ((d ^ 2 * omega G) ^ (2 ^ (d ^ 2))),
      ∀ i, IsUnionOfShiftColorable (2 ^ (d ^ 2)) (FASTournament.induce G {v | part v = i}) := by sorry

end SetDefinedGraphs
