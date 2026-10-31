-- Prove2me | Theorems.Thm_SteinerCutDominants_theorem_4
-- name    : SteinerCutDominants.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:06.878255+00:00
-- url     : https://prove2.me/theorems/993f3134-570b-4162-96f1-48ef5a55aaa2
-- title:
--   Theorem 4: finitely many irreducible Steiner graphs for each $|T|$
-- statement:
--   There is a function $f$ such that the number of irreducible facet inducing Steiner graphs $(G,T)$ is bounded by $f(|T|)$, up to isomorphisms.
--
--   This is the finiteness that underlies Main Result I.
--
--   Differences from the source:
--   - encoding: the number of isomorphism classes is at most f(|T|) → for each t a finite set of at most f t irreducible graphs with t terminals containing every such (G, T) up to isomorphism of (G, T); reason: such a family has one or more representatives per class and covers all classes, so the number of classes is at most f t
--   - encoding: (G, T) is irreducible → some weighted H on (G, T) is irreducible; reason: the unweighted notion is the existence of facet weights
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Theorem 4, p.11

import Mathlib
import Definitions.Def_SteinerCutDominants_IsIrreducible
import Definitions.Def_SteinerCutDominants_WSG_UIso

namespace SteinerCutDominants

/-- **Theorem 4** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.11). There is a
function `f` such that the number of irreducible facet inducing Steiner graphs `(G, T)` is bounded by
`f(|T|)` up to isomorphisms.

**Formalization Note** The count is through a family: for each `t`, a set of at most `f t` irreducible
graphs with `t` terminals that contains every such `(G, T)` up to isomorphism of `(G, T)`, weights
ignored. Hence the number of isomorphism classes is at most `f t`. -/
theorem theorem_4 :
    ∃ f : ℕ → ℕ, ∀ t : ℕ, ∃ 𝒢 : Set WSG, 𝒢.Finite ∧ 𝒢.ncard ≤ f t ∧
      (∀ H₀ ∈ 𝒢, IsIrreducible H₀ ∧ H₀.T.card = t) ∧
      ∀ H : WSG, IsIrreducible H → H.T.card = t → ∃ H₀ ∈ 𝒢, WSG.UIso H₀ H := by sorry

end SteinerCutDominants
