-- Prove2me | Theorems.Thm_PutermanMDP_Unichain_strict_bias_improvement
-- name    : PutermanMDP.Unichain.strict_bias_improvement
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:20.449817+00:00
-- url     : https://prove2.me/theorems/6098946b-a459-4e98-929f-6f331b27d7d4
-- title:
--   Proposition 8.6.5 — strict transient bias improvement
-- statement:
--   In the finite unichain model, let $(g,h)$ evaluate the incumbent rule $d$, and let $d'$ be chosen by step 3 as printed. Suppose $B(g,h)$ is zero at every state recurrent under $d'$ and positive at some state transient under $d'$. The source asserts that
--   $$\exists s\in T_{d'}:\quad h^{(d')^\infty}(s)>h^{d^\infty}(s).$$
--
--   The two biases are the canonical vectors $H_{d'}r_{d'}$ and $H_dr_d$. The printed assertion is retained; the counterexample under whole-rule tie retention is recorded separately in INSIGHTS.yaml. No statewise tie-retention hypothesis is inserted to repair it.
--
--   Differences from the source:
--   - encoding: finite nonempty state set and finite nonempty state-dependent action sets → finite types S and A, Nonempty S, and nonempty admissible finsets; reason: the union of finitely many finite action sets is finite; irrelevant action entries can be extended by zero rewards and any stochastic row
--   - encoding: standing finite unichain model of §8.6 with bounded rewards → IsUnichain M and a finite stationary MDP; reason: finiteness makes the reward bound automatic; no irreducibility or aperiodicity is added
--   - encoding: decision rules d_n and d_{n+1} and their evaluation solutions → admissible-rule subtypes d and d′, with explicit evaluation equations; reason: these are the algorithm variables and equations (8.6.1), not assumptions of improvement or termination
--   - encoding: P* is the Cesàro limit and H = (I − P + P*)⁻¹(I − P*) → published Cesàro limit and equivalent deviation matrix (I − P + P*)⁻¹ − P*; reason: for finite stochastic P, (I − P + P*)⁻¹P* = P*, so these are the same matrices, including periodic chains
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 382 (PDF 398), Proposition 8.6.5; proof continues p. 383 (PDF 399)

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_Iteration
open MarkovDecisionProcesses Matrix

namespace PutermanMDP.Unichain

/-- Proposition 8.6.5 as printed. The meaning of step 3 is exactly `Improves`;
no extra statewise tie-retention assumption is inserted. -/
theorem strict_bias_improvement {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M)
    (d d' : Rule M) (g : ℝ) (h : S → ℝ)
    (heval : Evaluates M d g h) (himp : Improves M d d' h)
    (hrec : ∀ s, IsRecurrent (transMatrix M d'.val) s →
      optimalityResidual M g h s = 0)
    (htrans : ∃ s, ¬ IsRecurrent (transMatrix M d'.val) s ∧
      0 < optimalityResidual M g h s) :
    ∃ s, ¬ IsRecurrent (transMatrix M d'.val) s ∧
      policyBias M d s < policyBias M d' s := by sorry

end PutermanMDP.Unichain
