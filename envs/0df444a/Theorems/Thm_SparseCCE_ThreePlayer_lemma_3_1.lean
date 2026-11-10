-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_1
-- name    : SparseCCE.ThreePlayer.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:24.398997+00:00
-- url     : https://prove2.me/theorems/ac92fc89-68dd-4bcc-9a89-0d7c33217126
-- title:
--   Lemma 3.1 — every-type-$\varepsilon_0$ BNE is PPAD-hard; small ex-ante regret is PPAD-hard under Assumption 1
-- statement:
--   There are rational constants $\varepsilon_0,\gamma\in(0,1)$ such that (a) computing an every-type-$\varepsilon_0$ BNE of a two-player, two-action Bayesian game is PPAD-hard, and (b) under Assumption 1, computing a Bayesian profile $y$ with ex-ante regret $\mathrm{Reg}(y)\le\gamma$ is PPAD-hard.
--
--   Differences from the source:
--   - encoding: the problems on two-player, two-action Bayesian games → EveryTypeBNEProblem ε0 and ExAnteRegretProblem γ: valid rational games by RatBayesGame.code; answers the codes of rational profiles; reason: a concrete binary code; answers are every rational solution
--   - reading: Assumption 1: bipartite polymatrix games, payoff range not stated → edge payoffs in [0, 1] (Assumption1); reason: constant regret thresholds ε*, δ* only make sense for normalized payoffs; the proof on p. 28 needs u_i ∈ [0, 1]
--   - encoding: PPAD-hard → CEPolytopeHard.PPADHard (every problem of QuasiStrictNE.PPAD reduces by CardinalMatching.SearchReduces); reason: the published platform definitions
--   - encoding: an explicitly given bipartite polymatrix game, including its isolated vertices → binary vertex counts followed by one marker per vertex and the edge/payoff list; reason: Prevents binary counts alone from succinctly encoding exponentially many isolated vertices while requiring an explicit mixed action for each vertex
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.1, p. 14; proof App. A.1, p. 28.

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_SparseCCE_ThreePlayer_BayesGame
import Definitions.Def_SparseCCE_ThreePlayer_Assumption1

namespace SparseCCE.ThreePlayer

/-- **Lemma 3.1 (Source problems)**, p. 14: there are rational constants `ε₀, γ ∈ (0, 1)` such that
the following problems on two-player, two-action Bayesian games are PPAD-hard, the second under
Assumption 1: (a) computing an every-type-`ε₀` BNE; (b) computing a Bayesian profile `y` with
`Reg(y) ≤ γ`. -/
theorem lemma_3_1 :
    ∃ ε₀ γ : ℚ, (0 < ε₀ ∧ ε₀ < 1) ∧ (0 < γ ∧ γ < 1) ∧
      CEPolytopeHard.PPADHard (EveryTypeBNEProblem ε₀) ∧
      (Assumption1 → CEPolytopeHard.PPADHard (ExAnteRegretProblem γ)) := by sorry

end SparseCCE.ThreePlayer
