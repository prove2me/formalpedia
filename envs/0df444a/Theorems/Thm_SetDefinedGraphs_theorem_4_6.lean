-- Prove2me | Theorems.Thm_SetDefinedGraphs_theorem_4_6
-- name    : SetDefinedGraphs.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:35.278241+00:00
-- url     : https://prove2.me/theorems/21ef0c93-4a6b-4485-a277-7c482c8dea8f
-- title:
--   Theorem 4.6 — cyclic clauses can be dropped: $\vec{\mathcal Y}_H=\vec{\mathcal Y}_F$
-- statement:
--   Let $H$ be an injective DNF and let $F$ be the DNF consisting of the acyclic clauses of $H$. Then
--   $$\vec{\mathcal Y}_H=\vec{\mathcal Y}_F .$$
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: F, the DNF of the acyclic clauses of H → any F with C ∈ F ↔ C ∈ H ∧ C acyclic; reason: this condition determines F uniquely
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 4.6, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Theorem 4.6** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.1, p.27, PDF p.29): let `H` be an injective DNF and let `F` be the DNF consisting of
the acyclic clauses of `H`. Then `Y⃗_H = Y⃗_F`.

**Formalization Note** `F` is given by its membership condition (`C ∈ F ↔ C ∈ H ∧ C` acyclic); the equality of
classes is stated digraph by digraph. -/
theorem theorem_4_6 {d : ℕ} (H : Finset (FullClause (Fin d))) (hH : IsInjectiveDNF H)
    (F : Finset (FullClause (Fin d))) (hF : ∀ C, C ∈ F ↔ C ∈ H ∧ IsAcyclicClause C)
    {W : Type} (G : Digraph W) : InY (dnfFun H) G ↔ InY (dnfFun F) G := by sorry

end SetDefinedGraphs
