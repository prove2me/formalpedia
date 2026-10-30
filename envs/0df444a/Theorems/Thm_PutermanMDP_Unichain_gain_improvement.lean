-- Prove2me | Theorems.Thm_PutermanMDP_Unichain_gain_improvement
-- name    : PutermanMDP.Unichain.gain_improvement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:19.640564+00:00
-- url     : https://prove2.me/theorems/aeac03a3-9c84-433a-9665-bff6fab0371a
-- title:
--   Proposition 8.6.1 — gain improvement
-- statement:
--   Consider the finite unichain model of §8.6. Let $d,d'$ be admissible stationary rules, let $(g,h)$ evaluate $d$ and $(g',h')$ evaluate $d'$, and suppose $d'$ maximizes $r_d+P_dh$. Write $B(g,h)$ for the optimality residual. Then
--   $$g'e=ge+P_{d'}^*B(g,h).$$
--   If $B(g,h)(s)>0$ at some state recurrent under $d'$, then $g'>g$. If $B(g,h)$ vanishes at every state recurrent under $d'$, then $g'=g$.
--
--   All three conclusions are included. This result separates improvements of the long-run average reward from changes confined to transient states. It does not need tie retention.
--
--   Differences from the source:
--   - encoding: finite nonempty state set and finite nonempty state-dependent action sets → finite types S and A, Nonempty S, and nonempty admissible finsets; reason: the union of finitely many finite action sets is finite; irrelevant action entries can be extended by zero rewards and any stochastic row
--   - encoding: standing finite unichain model of §8.6 with bounded rewards → IsUnichain M and a finite stationary MDP; reason: finiteness makes the reward bound automatic; no irreducibility or aperiodicity is added
--   - encoding: decision rules d_n and d_{n+1} and their evaluation solutions → admissible-rule subtypes d and d′, with explicit evaluation equations; reason: these are the algorithm variables and equations (8.6.1), not assumptions of improvement or termination
--   - encoding: P* is the Cesàro limit and H = (I − P + P*)⁻¹(I − P*) → published Cesàro limit and equivalent deviation matrix (I − P + P*)⁻¹ − P*; reason: for finite stochastic P, (I − P + P*)⁻¹P* = P*, so these are the same matrices, including periodic chains
--   - encoding: g_{d_n}, h_{d_n} in clause (c) → the same evaluation pair g,h as in clauses (a)–(b); reason: any two bias solutions differ by a constant, and the residual is invariant under that constant
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 379 (PDF 395), Proposition 8.6.1, (8.6.9)

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_Iteration
open MarkovDecisionProcesses Matrix

namespace PutermanMDP.Unichain

/-- Proposition 8.6.1, all three conclusions, in the finite unichain setting
of §8.6. No tie retention is needed for this proposition. -/
theorem gain_improvement {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M)
    (d d' : Rule M) (g g' : ℝ) (h h' : S → ℝ)
    (heval : Evaluates M d g h) (heval' : Evaluates M d' g' h')
    (himp : IsImproving M h d'.val) :
    (∀ s, g' = g + (policyLimit M d').mulVec (optimalityResidual M g h) s) ∧
    ((∃ s, IsRecurrent (transMatrix M d'.val) s ∧
        0 < optimalityResidual M g h s) → g < g') ∧
    ((∀ s, IsRecurrent (transMatrix M d'.val) s →
        optimalityResidual M g h s = 0) → g' = g) := by sorry

end PutermanMDP.Unichain
