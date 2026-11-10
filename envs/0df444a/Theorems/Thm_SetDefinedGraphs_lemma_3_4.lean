-- Prove2me | Theorems.Thm_SetDefinedGraphs_lemma_3_4
-- name    : SetDefinedGraphs.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:16.281746+00:00
-- url     : https://prove2.me/theorems/3d68b70a-919e-4b39-8f46-5c882b486d0c
-- title:
--   Lemma 3.4 — restriction to coordinates $I$ is a homomorphism
-- statement:
--   Let $C$ be a clause over the variables $q_{i,j}$, $i,j\in[d]$, let $I\subseteq[d]$, and let $V\subseteq\mathbb N^d$ be such that for all distinct $u,v\in V$ with $u|_I=v|_I$ the clause $C$ does not hold on $(u,v)$. Let $G$ be the realisation of $C$ over $V$ and $G'$ the realisation of $C|_I$ over $V|_I$. Then
--   $$G\ \text{is homomorphic to}\ G'.$$
--   The lemma lets the analysis of a clause pass to the coordinates in $I$; it is used for cyclic clauses (Lemma 4.5) and path clauses (Lemma 4.13).
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: a clause, a conjunction of literals → a pair of Boolean matrices (positive literals, negative literals); reason: every conjunction of literals is determined by which literals occur
--   - generalization: V ⊆ ℕ^d finite (realisations are over finite sets, p.2) → V : Set (Fin d → ℕ) arbitrary, possibly infinite; reason: the proof (u ↦ u|_I) never uses finiteness; finite V is a special case
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Lemma 3.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Lemma 3.4** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §3.3, p.17, PDF p.19): let `C` be a clause, `I ⊆ [d]`, and `V ⊆ ℕ^d` such that for all
distinct `u, v ∈ V`, if `u|_I = v|_I` then `C` does not hold on `(u, v)`. Let `G` be the realisation of `C` over
`V` and `G′` the realisation of `C|_I` over `V|_I`. Then `G` is homomorphic to `G′`.

**Formalization Note** A clause is a pair of positive/negative literal sets (`Clause`), not necessarily full; the
realisation is loopless (an arc needs distinct endpoints), the paper's convention for digraphs (p.14). -/
theorem lemma_3_4 {d : ℕ} (C : Clause (Fin d)) (I : Set (Fin d)) (V : Set (Fin d → ℕ))
    (hV : ∀ u ∈ V, ∀ v ∈ V, u ≠ v → restrictVec I u = restrictVec I v → ¬ C.Holds (eqPattern u v)) :
    Homomorphic (realisation C.toFun V) (realisation (C.restrict I).toFun (restrictSet I V)) := by sorry

end SetDefinedGraphs
