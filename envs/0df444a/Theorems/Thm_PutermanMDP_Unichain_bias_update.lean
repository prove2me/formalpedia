-- Prove2me | Theorems.Thm_PutermanMDP_Unichain_bias_update
-- name    : PutermanMDP.Unichain.bias_update
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:19.390023+00:00
-- url     : https://prove2.me/theorems/30b4decd-53ae-48be-9194-db5f48144cc6
-- title:
--   Proposition 8.6.3 — canonical bias update identity
-- statement:
--   In a finite unichain model let $(g,h)$ be any evaluation solution for the current admissible rule $d$, and let $d'$ be the rule selected by the improvement step. With the canonical biases $h^{d^\infty}=H_dr_d$ and $h^{(d')^\infty}=H_{d'}r_{d'}$,
--   $$h^{(d')^\infty}=h^{d^\infty}-P_{d'}^*h^{d^\infty}+H_{d'}B(g,h).$$
--
--   The evaluated vector $h$ may carry any additive constant; the biases appearing outside $B$ have their canonical normalization. The identity describes the transient part of a policy update.
--
--   Differences from the source:
--   - encoding: finite nonempty state set and finite nonempty state-dependent action sets → finite types S and A, Nonempty S, and nonempty admissible finsets; reason: the union of finitely many finite action sets is finite; irrelevant action entries can be extended by zero rewards and any stochastic row
--   - encoding: standing finite unichain model of §8.6 with bounded rewards → IsUnichain M and a finite stationary MDP; reason: finiteness makes the reward bound automatic; no irreducibility or aperiodicity is added
--   - encoding: decision rules d_n and d_{n+1} and their evaluation solutions → admissible-rule subtypes d and d′, with explicit evaluation equations; reason: these are the algorithm variables and equations (8.6.1), not assumptions of improvement or termination
--   - encoding: P* is the Cesàro limit and H = (I − P + P*)⁻¹(I − P*) → published Cesàro limit and equivalent deviation matrix (I − P + P*)⁻¹ − P*; reason: for finite stochastic P, (I − P + P*)⁻¹P* = P*, so these are the same matrices, including periodic chains
--   - reading: the introductory sentence says d_n is determined in the improvement step → d_{n+1} is the rule determined in that step; reason: (8.6.2), (8.6.10) and the proof on p. 381 identify the improved rule as d_{n+1}; this index typo is recorded in INSIGHTS.yaml
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 380 (PDF 396), Proposition 8.6.3, (8.6.10); proof p. 381 (PDF 397)

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_Iteration
open MarkovDecisionProcesses Matrix

namespace PutermanMDP.Unichain

/-- Proposition 8.6.3, (8.6.10). The printed `d_n` in the introductory sentence
is read as `d_{n+1}`, as required by (8.6.2) and the proof's residual identity. -/
theorem bias_update {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M)
    (d d' : Rule M) (g : ℝ) (h : S → ℝ)
    (heval : Evaluates M d g h) (himp : Improves M d d' h) :
    policyBias M d' = policyBias M d - (policyLimit M d').mulVec (policyBias M d) +
      (policyDeviation M d').mulVec (optimalityResidual M g h) := by sorry

end PutermanMDP.Unichain
