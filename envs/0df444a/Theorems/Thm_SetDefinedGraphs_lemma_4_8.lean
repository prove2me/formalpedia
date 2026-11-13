-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_8
-- name    : SetDefinedGraphs.lemma_4_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:26:36.461583+00:00
-- url     : https://prove2.me/theorems/bb099030-c322-4a2a-9f6c-45b292f91454
-- title:
--   Lemma 4.8 — $V_{L,a}$ is covered by at most $d^2\omega(G_{L,a})$ sets $U_{i,r}$
-- statement:
--   Let $D$ be a discrete clause over $q_{i,j}$, $i,j\in[d]$, with loop coordinates $L=L(D)\ne[d]$ (the standing assumption of p.27), and $\overline L=[d]\setminus L$.
--   Let $V\subseteq\mathbb N^{\underline d}$ be a finite injective set, $a\in\mathbb N^{\underline L}$, $G$ the realisation of $D$ over $V$ and $G_{L,a}=G[V_{L,a}]$. There exists a set $R\subseteq\mathbb N$ with
--   $$|R|\le d\cdot\omega(G_{L,a})$$
--   such that $V_{L,a}$ is the union of the at most $|\overline L|\cdot|R|\le d^2\cdot\omega(G_{L,a})$ (possibly empty) sets
--   $$U_{i,r}=\{v\in V_{L,a}: v_i=r\},\qquad i\in\overline L,\ r\in R.$$
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: G_{L,a} = G[V_{L,a}], G the realisation of D over V → the realisation of D over V_{L,a}; reason: the realisation over a subset of V is the induced subdigraph on it
--   - encoding: V ⊆ ℕ^d (the paper's digraphs are finite, p.2) → V : Set (Fin d → ℕ) with V.Finite; reason: the paper's realisations are finite digraphs; finiteness keeps ω (Mathlib cliqueNum) from being a junk value
--   - encoding: "the union of at most d² · ω(G_{L,a}) sets U_{i,r}, i ∈ L̄, r ∈ R" → V_{L,a} = ⋃_{i ∈ L̄, r ∈ R} U_{i,r} and |L̄|·|R| ≤ d²·ω(G_{L,a}); reason: the family U_{i,r} has |L̄|·|R| members
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.8, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.8** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.2, p.28, PDF p.30). Let `D` be a discrete clause with loop coordinates `L = L(D) ≠ [d]` (standing assumption, p.27), `L̄ = [d] ∖ L`, `V ⊆ ℕ^d̲` a finite injective set, `a ∈ ℕ^L̲`, and
`G_{L,a} = G[V_{L,a}]` where `G` is the realisation of `D` over `V`. There exists a set `R ⊆ ℕ` of size at most
`d · ω(G_{L,a})` such that `V_{L,a}` is the union of at most `d² · ω(G_{L,a})` (possibly empty) sets `U_{i,r}`,
`i ∈ L̄`, `r ∈ R`, where `U_{i,r} := {v ∈ V_{L,a} : v_i = r}`.

**Formalization Note** `G_{L,a}` is the realisation of `D` over `V_{L,a}`. The number of sets `U_{i,r}` is
`|L̄| · |R|`, bounded by `d² · ω(G_{L,a})`. Finiteness of `V` is the paper's (its digraphs are finite, p.2) and keeps
`ω` from being a junk value. -/
theorem lemma_4_8 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) (a : L → ℕ) (ha : Function.Injective a) :
    ∃ R : Finset ℕ, R.card ≤ d * omega (realisation (dnfFun {D}) (sliceSet V L a)) ∧
      Lᶜ.card * R.card ≤ d ^ 2 * omega (realisation (dnfFun {D}) (sliceSet V L a)) ∧
      sliceSet V L a = ⋃ i ∈ Lᶜ, ⋃ r ∈ R, {v | v ∈ sliceSet V L a ∧ v i = r} := by sorry

end SetDefinedGraphs
