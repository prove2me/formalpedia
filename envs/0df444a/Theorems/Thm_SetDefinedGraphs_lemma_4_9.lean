-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_9
-- name    : SetDefinedGraphs.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:30.371999+00:00
-- url     : https://prove2.me/theorems/68e24641-971d-4975-b0fa-0f3aa9711f1d
-- title:
--   Lemma 4.9 — $V$ is covered by at most $d^2\omega(G)$ $L$-functional sets
-- statement:
--   Let $D$ be a discrete clause over $q_{i,j}$, $i,j\in[d]$, with loop coordinates $L=L(D)\ne[d]$ (the standing assumption of p.27), and $\overline L=[d]\setminus L$.
--   Let $G=(V,E)$ be the realisation of $D$ over a finite injective set $V\subseteq\mathbb N^{\underline d}$. Then $V$ admits a covering by at most
--   $$d^2\cdot\omega(G)$$
--   sets each of which is $L$-functional.
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: V ⊆ ℕ^d (the paper's digraphs are finite, p.2) → V : Set (Fin d → ℕ) with V.Finite; reason: the paper's realisations are finite digraphs; finiteness keeps ω (Mathlib cliqueNum) from being a junk value
--   - encoding: a covering by at most N sets → a family U : Fin N → Set (ℕ^d) of subsets of V (possibly empty, overlapping) with union V; reason: a covering by at most N sets, indexed by [N]
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.9, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Functional

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.9** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.2, p.28, PDF p.30). Let `D` be a discrete clause with loop coordinates `L = L(D) ≠ [d]` (standing assumption, p.27), `L̄ = [d] ∖ L`, and `G = (V, E)` the realisation of `D` over a finite
injective set `V ⊆ ℕ^d̲`. The set `V` admits a covering by at most `d² · ω(G)` sets each of which is `L`-functional.

**Formalization Note** A covering by at most `N` sets is a family of subsets of `V` indexed by `Fin N` (some
possibly empty, overlaps allowed) whose union is `V`. -/
theorem lemma_4_9 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D) (hL : L ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) :
    ∃ U : Fin (d ^ 2 * omega (realisation (dnfFun {D}) V)) → Set (Fin d → ℕ),
      (∀ k, U k ⊆ V) ∧ (⋃ k, U k) = V ∧ ∀ k, IsLFunctional L (U k) := by sorry

end SetDefinedGraphs
