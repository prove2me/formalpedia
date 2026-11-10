-- Prove2me | Theorems.Thm_SetDefinedGraphs_theorem_1_2
-- name    : SetDefinedGraphs.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:46.671019+00:00
-- url     : https://prove2.me/theorems/7611f6ae-2d88-4b1c-ad99-8dfbb2c487a6
-- title:
--   Theorem 1.2 — every set-defined digraph splits into $\mathrm{poly}(\omega)$ parts, each a union of $\le c$ shift-colorable digraphs
-- statement:
--   Let $\vec{\mathcal X}$ be a set-defined class of digraphs. There exist a constant $c\in\mathbb N$ and a polynomial function $\tau:\mathbb N\to\mathbb N$ such that for every digraph $G=(V,E)\in\vec{\mathcal X}$:
--
--   1. the vertex set $V$ can be partitioned into at most $\tau(\omega(G))$ parts $V_1,\dots,V_r$, and
--   2. for each $i\in[r]$, the induced subdigraph $G[V_i]$ is the union of at most $c$ shift-colorable digraphs.
--
--   Both $c$ and $\tau$ depend only on the class, not on $G$. The theorem says that shift-colorable digraphs are the only obstruction to $\chi$-boundedness in set-defined classes: it implies that a set-defined class is $\chi$-bounded iff it is polynomially $\chi$-bounded (Corollary 1.3).
--
--   **Formalization Note** Every set-defined class is contained in a full class $\vec{\mathcal X}_f$, which is itself set-defined, so the statement is made for all $(d,f)$-set-defined digraphs, with $c$ and $\tau$ chosen from $(d,f)$ before $G$.
--
--   Differences from the source:
--
--   - encoding: "Let X⃗ be a set-defined class of digraphs" (X⃗ hereditary, X⃗ ⊆ X⃗_f for some d, f) → for every d and f, the statement for all digraphs of X⃗_f; reason: the conclusion passes to subclasses, and X⃗_f is itself a set-defined (hereditary) class; c and τ depend only on (d, f), i.e. on the class
--   - encoding: a polynomial function τ : ℕ → ℕ → τ ∈ ℕ[X], evaluated at ω(G); reason: a polynomial with natural coefficients is a polynomial function ℕ → ℕ, and every polynomial function ℕ → ℕ is bounded by one; the bound "at most τ(ω) parts" is monotone in τ
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: classes X⃗_f, X⃗′_f, Y⃗_f, X⃗_{f,P} of digraphs → predicates InX/InX'/InY/InXP on digraphs G : Digraph W, "G is isomorphic to the realisation over a finite V with the property"; reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
--   - encoding: a partition into at most N parts → a map V → Fin N (empty parts allowed); reason: a partition into at most N possibly empty parts is a labelling by [N]
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 1.2, pp.2–3 (PDF pp.4–5); restated p.23 (PDF p.25); proof p.30 (PDF p.32)

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

set_option autoImplicit false

namespace SetDefinedGraphs

/-- **Theorem 1.2** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1, pp.2–3, PDF pp.4–5; restated p.23, PDF p.25; proof p.30): let `X⃗` be a set-defined
class of digraphs. There exists a constant `c ∈ ℕ` and a polynomial function `τ : ℕ → ℕ` such that for every digraph
`G = (V, E) ∈ X⃗`:
1) the vertex set `V` can be partitioned into at most `τ(ω(G))` parts `V₁, …, V_r`, and
2) for each `i ∈ [r]`, the induced subdigraph `G[V_i]` is the union of at most `c` shift-colorable digraphs.

**Formalization Note** A set-defined class is contained in the full class `X⃗_f` of some `(d, f)`, and `X⃗_f` is itself
set-defined, so the statement is made for `X⃗_f` with `c` and `τ` depending only on `(d, f)`, chosen before `G`.
`τ` is a polynomial with natural-number coefficients (every polynomial function `ℕ → ℕ` is bounded by one, and the
bound "at most `τ(ω)` parts" is monotone in `τ`). A partition into at most `N` parts is a map `V → Fin N`. -/
theorem theorem_1_2 (d : ℕ) (f : (Fin d → Fin d → Bool) → Bool) :
    ∃ c : ℕ, ∃ τ : Polynomial ℕ, ∀ {W : Type} (G : Digraph W), InX f G →
      ∃ part : W → Fin (τ.eval (omega G)),
        ∀ i, IsUnionOfShiftColorable c (FASTournament.induce G {v | part v = i}) := by sorry

end SetDefinedGraphs
