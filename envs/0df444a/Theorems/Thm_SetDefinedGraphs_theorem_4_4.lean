-- Prove2me | Theorems.Thm_SetDefinedGraphs_theorem_4_4
-- name    : SetDefinedGraphs.theorem_4_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-09T22:27:29.889506+00:00
-- url     : https://prove2.me/theorems/9c8a2410-f843-4ff8-9fba-ae7f2e7a56b4
-- title:
--   Theorem 4.4 — reduction to at most $d^{2d}$ classes $\vec{\mathcal Y}_{H_i}$ of injective DNFs
-- statement:
--   Let $f:\{0,1\}^{d^2}\to\{0,1\}$. There exist at most $d^{2d}$ injective DNFs $H_1,\dots,H_r$, each over $(d'_i)^2$ variables for some $d'_i\le d$, such that every digraph $G\in\vec{\mathcal X}_f$ admits a partition
--   $$V(G)=V_1\cup\dots\cup V_r\qquad\text{with}\qquad G[V_i]\in\vec{\mathcal Y}_{H_i}\ \text{for every }i\in[r].$$
--   Furthermore, $\vec{\mathcal Y}_{H_i}\subseteq\vec{\mathcal X}_f$ for every $i$. The list $H_1,\dots,H_r$ depends only on $(d,f)$, not on $G$.
--
--   This is the first step of the decomposition theorem: it reduces an arbitrary set-defined class to boundedly many classes defined by injective DNFs over injective order-uniform sets.
--
--   Differences from the source:
--
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: a (full) DNF and its clauses → a Finset of full clauses, each its clause digraph Fin d → Fin d → Bool; the DNF holds on Q iff Q is one of its clauses; reason: a full clause holds exactly on the assignment equal to its clause digraph; a DNF is a set of clauses
--   - encoding: a partition into at most N parts → a map V → Fin N (empty parts allowed); reason: a partition into at most N possibly empty parts is a labelling by [N]
--   - reading: "each such Y⃗_{Hi} ⊂ X⃗f" → every digraph in Y⃗_{Hi} is in X⃗f (inclusion ⊆); reason: the proof (p.27) derives it as Y⃗_{Hi} ⊂ X⃗′_{Hi} = X⃗_{f,P} ⊂ X⃗_f, using ⊂ for ⊆; strictness is not claimed
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 4.4, p.26 (PDF p.28); proof pp.26–27

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Clauses

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Theorem 4.4** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §4.2, p.26, PDF p.28): let `f : {0,1}^{d²} → {0,1}`. There exist at most `d^{2d}` injective
DNFs `H₁, …, H_r`, each over `(d′)²` variables for some `d′ ≤ d`, so that every digraph `G ∈ X⃗_f` admits a partition
`V(G) = V₁ ∪ ⋯ ∪ V_r` such that `G[V_i] ∈ Y⃗_{H_i}` for every `i ∈ [r]`. Furthermore, each such `Y⃗_{H_i} ⊆ X⃗_f`.

**Formalization Note** The list `H₁, …, H_r` (and each `d′_i`) is chosen before `G`. The partition is a map
`V(G) → Fin r` (empty parts allowed; the empty digraph lies in every `Y⃗_H`). The paper's "`Y⃗_{H_i} ⊂ X⃗_f`" is
inclusion (its proof gives `Y⃗_{H_i} ⊂ X⃗′_{H_i} = X⃗_{f,P} ⊂ X⃗_f`, using `⊂` for `⊆`). `0^0 = 1`. -/
theorem theorem_4_4 {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) :
    ∃ r : ℕ, r ≤ d ^ (2 * d) ∧ ∃ d' : Fin r → ℕ, (∀ i, d' i ≤ d) ∧
      ∃ H : (i : Fin r) → Finset (FullClause (Fin (d' i))), (∀ i, IsInjectiveDNF (H i)) ∧
        (∀ {W : Type} (G : Digraph W), InX f G →
          ∃ part : W → Fin r, ∀ i, InY (dnfFun (H i)) (FASTournament.induce G {v | part v = i})) ∧
        (∀ (i : Fin r) {W : Type} (G : Digraph W), InY (dnfFun (H i)) G → InX f G) := by sorry

end SetDefinedGraphs
