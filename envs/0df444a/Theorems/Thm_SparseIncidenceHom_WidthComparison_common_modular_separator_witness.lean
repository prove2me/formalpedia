-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_common_modular_separator_witness
-- name    : SparseIncidenceHom.WidthComparison.common_modular_separator_witness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:02.631515+00:00
-- url     : https://prove2.me/theorems/b2e8cad5-dcb3-423f-bed5-20cca8d9c79d
-- title:
--   Lemma 3.3 — one modular weighting witnesses every fractional separator
-- statement:
--   Let $J$ be a finite covered hypergraph, $\gamma:E(J)\to[0,1]$ nonzero, and $0<\theta<1$. With $\beta_{J,\theta}(\gamma)$ denoting the optimum fractional separator cost, there exists an edge-dominated nonnegative real modular weighting $w\in M_J$ such that
--   $$\sum_{v\in V(J)}w_vx(v)\ge\beta_{J,\theta}(\gamma)
--   \quad\text{for every fractional }(\gamma,\theta)\text{-balanced separator }x.$$
--   The same weighting works simultaneously for every feasible separator. This is the source's $b$ with $w_v=b(\{v\})$ and $b(S)=\sum_{v\in S}w_v$. The witness is not allowed to depend on $x$, which is the feature needed for comparing separator cost with adaptive width.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: functions taking values in the real interval [0,1] → real-valued functions with coordinatewise interval inequalities; reason: the admissible functions are exactly the same, and the separator set sits in its ambient real vector space
--   - encoding: a modular set function b in M_J → its singleton coordinates w, with b(S) equal to the sum of w over S; reason: this is the defining bijection between the source modular functions and edge-dominated modular weight vectors
--   - encoding: attained minima defining fractional cover cost and optimum fractional separator cost → real infima of the feasible cover and separator cost sets; reason: coverage makes covers feasible with nonnegative costs, and compact separator feasibility with continuous cover value gives attainment; both infima equal the source minima
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 11, Lemma 3.3

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem common_modular_separator_witness {V : Type} [Fintype V]
    (J : FiniteHypergraph V) (γ : Edge J → ℝ) (hγ : IsEdgeWeight J γ)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ w : V → ℝ, IsModularWeight J w ∧
      ∀ x : V → ℝ, IsFractionalSeparator J γ θ x →
        separatorOptimum J γ θ ≤ ∑ v : V, w v * x v := by sorry

end SparseIncidenceHom.WidthComparison
