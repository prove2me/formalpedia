-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_separator_feasible_compact_convex
-- name    : SparseIncidenceHom.WidthComparison.separator_feasible_compact_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:02.652402+00:00
-- url     : https://prove2.me/theorems/bc8e3571-9431-4bab-878f-ab01a738d25c
-- title:
--   Lemma 3.2 — fractional separators form a nonempty compact convex set
-- statement:
--   Let $J$ be a finite covered hypergraph, let $\gamma:E(J)\to[0,1]$ be nonzero, and let $0<\theta<1$. Write $\mathcal X_{J,\gamma,\theta}$ for the fractional balanced separators defined by the endpoint-inclusive truncated primal distances. Then
--   $$\mathcal X_{J,\gamma,\theta}\ne\varnothing,\qquad
--   \mathcal X_{J,\gamma,\theta}\text{ is compact},\qquad
--   \mathcal X_{J,\gamma,\theta}\text{ is convex}.$$
--   Compactness is for the usual finite product topology on $\mathbb R^{V(J)}$, and convexity is over $\mathbb R$. The assertion includes all three properties for every threshold in the open unit interval. It supplies the feasible-set geometry needed for the common modular witness.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: functions taking values in the real interval [0,1] → real-valued functions with coordinatewise interval inequalities; reason: the admissible functions are exactly the same, and the separator set sits in its ambient real vector space
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 11, Lemma 3.2

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem separator_feasible_compact_convex {V : Type} [Fintype V]
    (J : FiniteHypergraph V) (γ : Edge J → ℝ) (hγ : IsEdgeWeight J γ)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (fractionalSeparators J γ θ).Nonempty ∧
    IsCompact (fractionalSeparators J γ θ) ∧ Convex ℝ (fractionalSeparators J γ θ) := by sorry

end SparseIncidenceHom.WidthComparison
