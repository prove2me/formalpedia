-- Prove2me | Theorems.Thm_SetDefinedGraphs_theorem_4_12
-- name    : SetDefinedGraphs.theorem_4_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:26:29.067116+00:00
-- url     : https://prove2.me/theorems/99bfdc05-9fa2-4824-a2d7-2fd4d2faf4d7
-- title:
--   Theorem 4.12 — discrete DNFs: a partition into $(d^2\omega(G))^k$ functional independent sets
-- statement:
--   Let $F$ be a discrete DNF with clauses $D_1,\dots,D_k$ and $L_i=L(D_i)$, where $L_i\ne[d]$ for every $i$ (the standing assumption of p.27). Then for every realisation $G=(V,E)$ of $F$ over a finite injective set $V\subseteq\mathbb N^{\underline d}$, the vertex set can be partitioned into at most
--   $$(d^2\cdot\omega(G))^k$$
--   independent sets each of which is $(L_1,\dots,L_k)$-functional.
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: V ⊆ ℕ^d (the paper's digraphs are finite, p.2) → V : Set (Fin d → ℕ) with V.Finite; reason: the paper's realisations are finite digraphs; finiteness keeps ω (Mathlib cliqueNum) from being a junk value
--   - encoding: a partition into at most N parts → a map V → Fin N (empty parts allowed); reason: a partition into at most N possibly empty parts is a labelling by [N]
--   - encoding: the clauses D1, …, Dk of F → F is a Finset of clauses and k = |F|; reason: a DNF is a set of distinct clauses
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 4.12, p.29 (PDF p.31); standing assumption p.27

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Functional

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Theorem 4.12** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.2, p.29, PDF p.31): let `F` be a discrete DNF, `D₁, …, D_k` the clauses of `F`, and
`L_i := L(D_i)`, `i ∈ [k]` (with `L_i ≠ [d]`, the standing assumption of p.27). Then, for every realisation
`G = (V, E)` of `F` over a set `V ⊆ ℕ^d̲`, its vertex set can be partitioned into at most `(d² · ω(G))^k` independent
sets each of which is `(L₁, …, L_k)`-functional.

**Formalization Note** `F` is a finite set of discrete full clauses, so `k = |F|`. A partition into at most `N` sets
is a map `V → Fin N`. `(L₁, …, L_k)`-functional means `L_s`-functional for every `s` (each with its own `λ_s`).
`V` is finite (the paper's digraphs are finite, p.2), which keeps `ω` from being a junk value. -/
theorem theorem_4_12 {d : ℕ} (F : Finset (FullClause (Fin d))) (hF : IsDiscreteDNF F)
    (hL : ∀ D ∈ F, loopCoords D ≠ Finset.univ)
    (V : Set (Fin d → ℕ)) (hVfin : V.Finite) (hV : IsInjectiveSet V) :
    ∃ part : V → Fin ((d ^ 2 * omega (realisation (dnfFun F) V)) ^ F.card),
      ∀ s, IsIndependent (realisation (dnfFun F) V) {x | part x = s} ∧
        ∀ D ∈ F, IsLFunctional (loopCoords D) {v | ∃ h : v ∈ V, part ⟨v, h⟩ = s} := by sorry

end SetDefinedGraphs
