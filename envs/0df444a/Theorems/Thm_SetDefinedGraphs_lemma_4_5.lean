-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_5
-- name    : SetDefinedGraphs.lemma_4_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:30:27.34169+00:00
-- url     : https://prove2.me/theorems/75b5931f-9062-4f58-bae3-c558bd6dbcd0
-- title:
--   Lemma 4.5 — cyclic clauses give edgeless digraphs on order-uniform sets
-- statement:
--   Let $C$ be a cyclic clause, i.e. an injective full clause whose clause digraph contains a directed cycle on at least two vertices. Then every digraph in $\vec{\mathcal Y}_C$ is edgeless.
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: Y⃗_C for a clause C → Y⃗ of the one-clause DNF {C}; reason: a clause is a one-clause DNF
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.5, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.5** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.1, p.27, PDF p.29): let `C` be a cyclic clause. Then any digraph in `Y⃗_C` is edgeless.

**Formalization Note** `C` is a full injective clause whose clause digraph contains a directed cycle on at least two
vertices (`IsCyclicClause`); `Y⃗_C` is `Y⃗` of the one-clause DNF `{C}`. -/
theorem lemma_4_5 {d : ℕ} (C : FullClause (Fin d)) (hC : IsCyclicClause C) {W : Type} (G : Digraph W)
    (hG : InY (dnfFun {C}) G) : ∀ a b, ¬ G.Adj a b := by sorry

end SetDefinedGraphs
