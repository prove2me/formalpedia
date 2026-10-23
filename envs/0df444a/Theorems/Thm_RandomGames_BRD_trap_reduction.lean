-- Prove2me | Theorems.Thm_RandomGames_BRD_trap_reduction
-- name    : RandomGames.BRD.trap_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:57.570986+00:00
-- url     : https://prove2.me/theorems/b9b4dd6a-bef8-4103-8375-0d5a5798d116
-- title:
--   Proof of Theorem 3.4, p. 21, with (3.10), p. 10 — best-response dynamics fails to converge to a PNE exactly when it visits a trap
-- statement:
--   Fix $N$ and a payoff family $Z=(Z^{\boldsymbol s}_i)$, and run best-response dynamics $\mathsf{BR}^{(N)}$ from $\mathbf 0$ on the partially oriented hypercube $\vec{\mathscr H}^\beta_N$ determined by $Z$. Then $\mathsf{BR}^{(N)}$ does not converge to a PNE if and only if it visits a trap; in terms of probabilities given $Z$,
--   $$\mathsf P\bigl(\mathsf{BR}^{(N)}\text{ does not converge to a PNE}\mid Z\bigr) = \mathsf P\bigl(\exists k:\ \mathsf{BR}^{(N)}_k \in \textstyle\bigcup_{T\text{ trap}} T \mid Z\bigr).$$
--
--   In particular, if $\vec{\mathscr H}^\beta_N$ has no trap, $\mathsf{BR}^{(N)}$ converges to a PNE with probability one. The proof of Theorem 3.4 uses this to reduce (3.9) to the absence of traps (5.24). The chain cannot leave a trap once it enters it, which is (3.10).
--
--   **Formalization Note** The statement is deterministic in the payoffs. The left side is `notConvProb Z`, built from the chain that stays put at a PNE (see the definition `RandomGames.BRD.Game`). Since the union of the traps is closed under the dynamics, the probability of visiting it is the supremum over $k$ of the probability of being in it at time $k$, which is how the right side is written.
-- source:
--   Amiet, Collevecchio, Scarsini & Zhong, Pure Nash Equilibria and Best-Response Dynamics in Random Games, arXiv:1905.10758v4, p. 21, proof of Theorem 3.4 (first sentence); (3.10), p. 10; Definition 3.5, p. 10

import Mathlib
import Definitions.Def_RandomGames_BRD_Game

namespace RandomGames.BRD

/-- Proof of Theorem 3.4, p. 21, with (3.10), p. 10: `BR^(N)` does not converge to a PNE if and
only if it visits a trap. Given the payoffs, the probability of non-convergence equals the
probability that the chain is in (the vertex set of) some trap at some time. -/
theorem trap_reduction (N : ℕ) (Z : Fin N → Profile N → ℝ) :
    notConvProb Z =
      ⨆ k, (brdLaw Z k).toOuterMeasure {s | ∃ T : Finset (Profile N), IsTrap Z T ∧ s ∈ T} := by sorry

end RandomGames.BRD
