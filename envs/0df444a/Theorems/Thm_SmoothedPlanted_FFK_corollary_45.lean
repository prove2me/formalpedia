-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_corollary_45
-- name    : SmoothedPlanted.FFK.corollary_45
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:34:01.352217+00:00
-- url     : https://prove2.me/theorems/8cd55d36-ff8d-4757-9c4c-09bf29af911a
-- title:
--   Corollary 45 — weak duality for the Robust Theta SDP
-- statement:
--   For a finite simple graph $G$, natural $k$ and real $\Delta>0$, every feasible dual solution $(\alpha,\beta,\mu,\gamma,N)$ of (D) satisfies
--   $$\Theta'(G,k,\Delta)\le\alpha+\beta k(k-1)+2\mu\Delta.$$
--   The dual slack is the concrete matrix defined in (D), with symmetric nonnegative $N$ and $\beta,\mu\ge0$.
--
--   Differences from the source:
--   - encoding: arbitrary finite graph vertices → vertices indexed by Fin n; reason: every finite graph admits such a relabelling
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
--   - encoding: dual slack written as a sum of indicator matrices → dual slack specified entry by entry; reason: the off-diagonal first row is −(γ_v+1)/2, and the lower block is diag(γ)+β(J−I)+μA−N
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Corollary 45, printed p. 29 (PDF p. 31), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Dual

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem corollary_45 {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (Δ : ℝ)
    (hΔ : 0 < Δ) (α β μ : ℝ) (γ : Fin n → ℝ) (N : Matrix (Fin n) (Fin n) ℝ)
    (hdual : dualFeasible G α β μ γ N) :
    thetaPrime G k Δ ≤ α + β * (k : ℝ) * ((k : ℝ) - 1) + 2 * μ * Δ := by sorry

end SmoothedPlanted.FFK
