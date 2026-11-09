-- Prove2me | Theorems.Thm_SparseIncidenceHom_WidthComparison_round_fractional_separator
-- name    : SparseIncidenceHom.WidthComparison.round_fractional_separator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:39.222609+00:00
-- url     : https://prove2.me/theorems/cdace583-fe6d-49f1-b278-88f8fca2299e
-- title:
--   Proposition 3.5 — one rounded separator satisfies both structural bounds
-- statement:
--   There exists a universal constant $C_0>0$ such that the following holds for every finite covered hypergraph $J$, every nonzero real weighting $\gamma:E(J)\to[0,1]$, and every fractional $(\gamma,1/2)$-balanced separator $x$. There is a single integral $(\gamma,5/6)$-balanced separator $S\subseteq V(J)$ satisfying both
--   $$\rho_J^*(S)\le C_0\mu(J)\rho_J^*(x)\log_2\max\{2,\rho_J^*(x)\},$$
--   $$\rho_J^*(S)\le C_0\max\{1,\log_2\alpha(J)\}\rho_J^*(x)\log_2\max\{2,\rho_J^*(x)\}.$$
--   The same $C_0$ works across all carriers, hypergraphs, weightings, separators, and both inequalities. Zero fractional cost is included. The invariants are incidence degeneracy and primal independence number. This result supplies the integral separator needed by the width comparison without assuming any rounding procedure as a hypothesis.
--
--   Differences from the source:
--   - encoding: finite hypergraphs with the standing coverage and nonempty-edge conventions → Mathlib hypergraphs on an arbitrary finite carrier, with the full carrier as vertex set and explicit coverage and nonempty-edge fields; reason: every source hypergraph is represented by choosing its vertex set as carrier, including empty and disconnected induced hypergraphs
--   - encoding: functions taking values in the real interval [0,1] → real-valued functions with coordinatewise interval inequalities; reason: the admissible functions are exactly the same, and the separator set sits in its ambient real vector space
--   - encoding: a universal constant C_0 → a positive universal real constant C_0; reason: a universal bound can be enlarged to a positive constant since every multiplying factor is nonnegative; no source instance or bound is lost
--   - encoding: attained minimum defining fractional cover cost → real infimum of the feasible cover cost set; reason: finite coverage supplies feasible covers, and a compact nonnegative cost sublevel gives attainment, so the infimum equals the source minimum
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), p. 13, Proposition 3.5 ([KLS+24, Theorem 5.6])

import Mathlib
import Definitions.Def_SparseIncidenceHom_WidthComparison_Separators

namespace SparseIncidenceHom.WidthComparison

theorem round_fractional_separator :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (V : Type) [Fintype V] (J : FiniteHypergraph V)
      (γ : Edge J → ℝ), IsEdgeWeight J γ →
      ∀ x : V → ℝ, IsFractionalSeparator J γ (1 / 2) x →
      ∃ S : Set V, IsIntegralSeparator J γ (5 / 6) S ∧
        setCoverCost J S ≤ C₀ * (incidenceDegeneracy J : ℝ) * coverCost J x *
          logTwo (max 2 (coverCost J x)) ∧
        setCoverCost J S ≤ C₀ * max 1 (logTwo (independenceNumber J : ℝ)) * coverCost J x *
          logTwo (max 2 (coverCost J x)) := by sorry

end SparseIncidenceHom.WidthComparison
