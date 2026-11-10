-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_7
-- name    : SetDefinedGraphs.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:23.170173+00:00
-- url     : https://prove2.me/theorems/3e1273df-c765-4143-9645-3b8827a133f6
-- title:
--   Lemma 4.7 — non-adjacency in $G_{L,a}$ is a shared non-loop value
-- statement:
--   Let $D$ be a discrete clause over $q_{i,j}$, $i,j\in[d]$, with loop coordinates $L=L(D)\ne[d]$ (the standing assumption of p.27), and $\overline L=[d]\setminus L$.
--   Let $V\subseteq\mathbb N^{\underline d}$ be an injective set, $a\in\mathbb N^{\underline L}$, $G$ the realisation of $D$ over $V$, and $G_{L,a}=G[V_{L,a}]$. Two distinct vertices $v,w$ of $G_{L,a}$ are non-adjacent (no arc in either direction) if and only if
--   $$v(\overline L)\cap w(\overline L)\ne\emptyset .$$
--   Injectivity of $V$ is needed: for $d=2$, $D=q_{1,1}\wedge\overline{q_{1,2}}\wedge\overline{q_{2,1}}\wedge\overline{q_{2,2}}$, $v=(1,1)$, $w=(1,2)$ are non-adjacent with $v(\overline L)\cap w(\overline L)=\emptyset$.
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: G_{L,a} = G[V_{L,a}], G the realisation of D over V → the realisation of D over V_{L,a}; reason: the realisation over a subset of V is the induced subdigraph on it
--   - reading: "two vertices v and w"; "non-adjacent" → distinct v ≠ w; no arc v → w and no arc w → v; reason: adjacency of two vertices of a digraph means an arc in either direction, and the statement concerns pairs of distinct vertices
--   - generalization: V ⊆ ℕ^d̲ finite (realisations are over finite sets, p.2) → V an arbitrary, possibly infinite, injective set; reason: the proof (p.28) compares the literals of D on one pair (v, w) and never uses finiteness; finite V is a special case
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.7, p.28 (PDF p.30); setting p.28

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.7** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.2, p.28, PDF p.30). Let `D` be a discrete clause with loop coordinates `L = L(D) ≠ [d]` (standing assumption, p.27), `L̄ = [d] ∖ L`, `V ⊆ ℕ^d̲` an injective set, `a ∈ ℕ^L̲`, and
`G_{L,a} = G[V_{L,a}]` where `G` is the realisation of `D` over `V`. Two vertices `v` and `w` in `G_{L,a}` are
non-adjacent if and only if `v(L̄) ∩ w(L̄) ≠ ∅`.

**Formalization Note** `G_{L,a}` is the realisation of `D` over `V_{L,a}` (the realisation over a subset is the
induced subdigraph). "Two vertices" are distinct; "non-adjacent" means no arc in either direction.
`v(L̄) ∩ w(L̄) ≠ ∅` is `∃ i, j ∉ L, v_i = w_j`. -/
theorem lemma_4_7 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hV : IsInjectiveSet V) (a : L → ℕ) (ha : Function.Injective a)
    (v w : Fin d → ℕ) (hv : v ∈ sliceSet V L a) (hw : w ∈ sliceSet V L a) (hvw : v ≠ w) :
    (¬ (realisation (dnfFun {D}) (sliceSet V L a)).Adj ⟨v, hv⟩ ⟨w, hw⟩ ∧
        ¬ (realisation (dnfFun {D}) (sliceSet V L a)).Adj ⟨w, hw⟩ ⟨v, hv⟩) ↔
      ∃ i ∉ L, ∃ j ∉ L, v i = w j := by sorry

end SetDefinedGraphs
