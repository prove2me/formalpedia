-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_3
-- name    : SetDefinedGraphs.lemma_4_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:27:47.473458+00:00
-- url     : https://prove2.me/theorems/b91dc0d0-42d5-4893-81d7-df8cbfe56f99
-- title:
--   Lemma 4.3 — $\vec{\mathcal X}_{f,P}=\vec{\mathcal X}'_H$ for an injective DNF $H$
-- statement:
--   Let $f:\{0,1\}^{d^2}\to\{0,1\}$ and let $P$ be a partition of $[d]$. Then there exist $d'\le d$ and an injective DNF $H$ over $(d')^2$ variables such that
--   $$\vec{\mathcal X}_{f,P}=\vec{\mathcal X}'_H .$$
--   Thus the digraphs realised over $P$-homogeneous sets are exactly those realised by an injective DNF over injective sets.
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: a partition P of [d] → P : Setoid (Fin d); reason: partitions and equivalence relations correspond bijectively
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.3, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.3** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.2, p.26, PDF p.28): let `f : {0,1}^{d²} → {0,1}`, and let `P` be a partition of `[d]`.
Then there exists an injective DNF `H` over `(d′)²` variables, for some `d′ ≤ d`, such that `X⃗_{f,P} = X⃗′_H`.

**Formalization Note** `H` is a finite set of injective full clauses over `Fin d′`; the equality of classes is
equality of isomorphism-closed classes of digraphs: a digraph lies in one iff it lies in the other. -/
theorem lemma_4_3 {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) (P : Setoid (Fin d)) :
    ∃ d' : ℕ, d' ≤ d ∧ ∃ H : Finset (FullClause (Fin d')), IsInjectiveDNF H ∧
      ∀ {W : Type} (G : Digraph W), InXP f P G ↔ InX' (dnfFun H) G := by sorry

end SetDefinedGraphs
