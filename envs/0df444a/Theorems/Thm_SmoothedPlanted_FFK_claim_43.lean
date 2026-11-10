-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_claim_43
-- name    : SmoothedPlanted.FFK.claim_43
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:58.13293+00:00
-- url     : https://prove2.me/theorems/f808bea1-a2ee-40fc-851f-5626327ea802
-- title:
--   Claim 43 — dropping constraint (7) and the variable-conflict edges can only increase the SDP value
-- statement:
--   For a pairwise CSP instance, any planted set $S$, natural $k$, and real $\Delta>0$, let $H'$ be the incompatibility graph with all same-variable edges deleted. Then
--   $$\Theta(H_{V\setminus S},k,\Delta)\le\Theta'(H'_{V\setminus S},k,\Delta).$$
--   The right-hand program has no per-variable mass constraint.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: unit u and vectors w in arbitrary finite dimension → positive semidefinite Gram matrix indexed by Option of the vertex type (literals in the lifted program); reason: every such vector family has this Gram matrix and each PSD matrix has a finite-dimensional realization; none is u
--   - encoding: sum over unordered edges and ordered distinct literal pairs → one half of the adjacency sum and the full ordered distinct-pair sum; reason: symmetric Gram entries count each unordered edge twice; the bounds remain Δ and k(k−1)
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Claim 43, printed p. 27 (PDF p. 29), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Theta
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem claim_43 {n q : ℕ} (Y : CSP (Fin n) q) (S : Finset (Fin n))
    (k : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) :
    theta (incompatibility (restrictCSP Y Sᶜ)) k Δ ≤
      thetaPrime (incompatibilityPrime (restrictCSP Y Sᶜ)) k Δ := by sorry

end SmoothedPlanted.FFK
