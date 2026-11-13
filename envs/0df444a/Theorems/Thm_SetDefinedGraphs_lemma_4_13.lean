-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_13
-- name    : SetDefinedGraphs.lemma_4_13
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:27:43.83494+00:00
-- url     : https://prove2.me/theorems/d85bd1a4-04bf-4e32-b2ba-64a5478ae5e1
-- title:
--   Lemma 4.13 — path clauses give shift-colorable digraphs; $\omega\le2$
-- statement:
--   Let $P$ be a path clause. Then every digraph $G\in\vec{\mathcal Y}_P$ is shift-colorable. In particular,
--   $$\omega(G)\le2 .$$
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: Y⃗_P for a clause P → Y⃗ of the one-clause DNF {P}; reason: a clause is a one-clause DNF
--   - encoding: a homomorphism to a shift digraph (an induced subdigraph of S⃗(n,2)) → a homomorphism to S⃗(n,2) for some n; reason: equivalent: compose with the inclusion; S⃗(n,2) is itself a shift digraph
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.13, p.29 (PDF p.31); proof pp.29–30

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.13** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.3, p.29, PDF p.31): let `P` be a path clause. Then any digraph `G ∈ Y⃗_P` is
shift-colorable. In particular, `ω(G) ≤ 2`. -/
theorem lemma_4_13 {d : ℕ} (P : FullClause (Fin d)) (hP : IsPathClause P) {W : Type} (G : Digraph W)
    (hG : InY (dnfFun {P}) G) : IsShiftColorable G ∧ omega G ≤ 2 := by sorry

end SetDefinedGraphs
