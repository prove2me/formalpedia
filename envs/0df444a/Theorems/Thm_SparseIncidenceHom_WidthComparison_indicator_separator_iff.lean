-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_indicator_separator_iff
-- name    : SparseIncidenceHom.WidthComparison.indicator_separator_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:19.567497+00:00
-- url     : https://prove2.me/theorems/57078414-0c22-45a5-8cae-ab18197be54c
-- title:
--   Lemma 3.1 — integral balance is equivalent to fractional indicator balance
-- statement:
--   Let $J$ be a finite covered hypergraph, let $S\subseteq V(J)$, let $\gamma:E(J)\to[0,1]$ be nonzero, and let $0<\theta<1$. For the indicator $\mathbf1_S$,
--   $$\mathbf1_S\text{ is fractionally }(\gamma,\theta)\text{-balanced}
--   \quad\Longleftrightarrow\quad S\text{ is integrally }(\gamma,\theta)\text{-balanced}.$$
--   Integral balance counts every original edge meeting a remaining primal component, including edges also meeting $S$. Fractional distances include endpoints and zero-length paths. The equivalence connects set separators to the continuous relaxation and includes both implications.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: functions taking values in the real interval [0,1] → real-valued functions with coordinatewise interval inequalities; reason: the admissible functions are exactly the same, and the separator set sits in its ambient real vector space
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 10, Lemma 3.1 ([KLS+24, Fact 5.4])

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem indicator_separator_iff {V : Type} [Fintype V]
    (J : FiniteHypergraph V) (S : Set V) (γ : Edge J → ℝ) (hγ : IsEdgeWeight J γ)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    IsFractionalSeparator J γ θ (indicator S) ↔ IsIntegralSeparator J γ θ S := by sorry

end SparseIncidenceHom.WidthComparison
