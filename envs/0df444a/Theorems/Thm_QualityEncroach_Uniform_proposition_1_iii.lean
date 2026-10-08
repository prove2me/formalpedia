-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_proposition_1_iii
-- name    : QualityEncroach.Uniform.proposition_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:34.121598+00:00
-- url     : https://prove2.me/theorems/38d87979-190a-481a-9c1b-cd8a544feffc
-- title:
--   Proposition 1(iii), p. 11 — when encroachment happens, Π^U_M > Π^N_M = 1/(54k) and Π^U_R < Π^N_R = 1/(108k)
-- statement:
--   Let $k>0$ be the manufacturer's cost of quality and $c\ge 0$ her direct selling cost. Consider any subgame perfect equilibrium of the encroachment game with uniform quality in which the manufacturer encroaches, i.e. sells a positive quantity $q^U_M>0$ through her direct channel on the equilibrium path. Then the manufacturer's equilibrium profit strictly exceeds her benchmark profit without a direct channel, and the retailer's equilibrium profit is strictly below his benchmark profit:
--   $$\Pi^U_M>\Pi^N_M=\frac{1}{54k},\qquad \Pi^U_R<\Pi^N_R=\frac{1}{108k}.$$
--
--   With exogenous quality, encroachment can make both firms better off (Arya et al. 2007); this result says that once the manufacturer chooses quality, a win–win outcome is no longer possible: the manufacturer always wins and the retailer always loses.
--
--   **Formalization Note.** The benchmark profits $1/(54k)$ and $1/(108k)$ are the paper's constants (p. 9); the milestone `benchmark_equilibrium` proves that they are the profits of every subgame perfect equilibrium of the benchmark game and that one exists.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 11, Proposition 1(iii); benchmark profits p. 9; proof p. 29

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- Proposition 1(iii), p. 11: in every subgame perfect equilibrium of the encroachment game
with uniform quality in which the manufacturer encroaches (`q^U_M > 0` on the path), the
manufacturer earns strictly more than her benchmark profit `Π^N_M = 1/(54k)` and the retailer
strictly less than his benchmark profit `Π^N_R = 1/(108k)` (p. 9). -/
theorem proposition_1_iii (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c σ) (henc : 0 < σ.path.qM) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by sorry

end QualityEncroach.Uniform
