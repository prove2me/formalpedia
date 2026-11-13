-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_4_10
-- name    : SetDefinedGraphs.lemma_4_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:26:59.405521+00:00
-- url     : https://prove2.me/theorems/6eff973e-90e4-4ad3-bb68-3acf42e80691
-- title:
--   Lemma 4.10 — $L$-functional sets are independent
-- statement:
--   Let $D$ be a discrete clause over $q_{i,j}$, $i,j\in[d]$, with loop coordinates $L=L(D)$, let $G=(V,E)$ be the realisation of $D$ over a set $V\subseteq\mathbb N^d$, and let $U\subseteq V$ be an $L$-functional set. Then
--   $$U\ \text{is an independent set in}\ G.$$
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - generalization: G ∈ Y⃗_D, the realisation of D over a finite set V ⊆ ℕ^d̲ (injective; order-uniform by G ∈ Y⃗_D) → the realisation of D over an arbitrary (possibly infinite, non-injective) set V ⊆ ℕ^d; reason: the proof (pp.28–29) uses only the literals q_{i,i}, i ∈ L, and q̄_{λ,λ}; injective order-uniform sets are a special case
--   - encoding: standing assumption L(D) ≠ [d] → implied by the hypothesis that U is L-functional (λ ∈ L̄); reason: L-functionality requires some λ ∉ L
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 4.10, p.28 (PDF p.30); proof pp.28–29

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Functional

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 4.10** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.3.2, p.28, PDF p.30). Let `D` be a discrete clause with loop coordinates `L = L(D)`, let
`G = (V, E)` be the realisation of `D` over a set `V`, and let `U ⊆ V` be an `L`-functional set. Then `U` is an
independent set in `G`.

**Formalization Note** The paper takes `G ∈ Y⃗_D` realised over an injective `V ⊆ ℕ^d̲`; the statement here holds for
every `V ⊆ ℕ^d` (a generalization, see the differences list). `L ≠ [d]` is implied by `L`-functionality. -/
theorem lemma_4_10 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D)
    (V : Set (Fin d → ℕ)) (U : Set (Fin d → ℕ)) (hUV : U ⊆ V) (hU : IsLFunctional L U) :
    IsIndependent (realisation (dnfFun {D}) V) {x | x.1 ∈ U} := by sorry

end SetDefinedGraphs
