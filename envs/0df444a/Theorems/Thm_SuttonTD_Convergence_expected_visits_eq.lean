-- Prove2me | Theorems.Thm_SuttonTD_Convergence_expected_visits_eq
-- name    : SuttonTD.Convergence.expected_visits_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:50:11.164567+00:00
-- url     : https://prove2.me/theorems/ba842610-5fe7-47fb-a5ed-487533455daf
-- title:
--   (7) — expected visit counts $d^\top=\mu^\top(I-Q)^{-1}$
-- statement:
--   Let $C$ be an absorbing Markov chain started from a distribution $\mu$ on the nonterminal states ($\mu_i\ge0$, $\sum_i\mu_i=1$), and let $d_i$ be the expected number of times the chain is in state $i$ during one sequence. Then
--
--   $$d^\top=\mu^\top(I-Q)^{-1}.$$
--
--   Precisely: the family $(s,j)\mapsto \Pr(s,j)\cdot\#\{t:s_t=i\}$, indexed by finite lists $s$ of nonterminal states and terminal states $j$, is summable, with sum $[\mu^\top(I-Q)^{-1}]_i$.
--
--   This gives the diagonal matrix $D$ of the mean TD(0) dynamics in closed form.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, (7), p. 25 (PDF p. 17)

import Definitions.Def_SuttonTD_Convergence_ExpectedVisits
open Matrix

namespace SuttonTD.Convergence

/-- **Expected visit counts (7)** (Sutton 1988, §4.1, p. 25, PDF p. 17): for an absorbing Markov
chain started from the distribution `μ`, the expected number `d_i` of times the chain is in the
nonterminal state `i` in one sequence satisfies `dᵀ = μᵀ(I − Q)⁻¹`.

Formally: the family `(s, j) ↦ P(sequence = s, terminal = j) · #{t : s_t = i}`, indexed by all
finite lists `s` of nonterminal states and terminal states `j`, is summable with sum
`[μᵀ(I − Q)⁻¹]_i`. In particular `expectedVisits C μ i = [μᵀ(I − Q)⁻¹]_i`. -/
theorem expected_visits_eq {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1) (i : N) :
    HasSum (fun p : List N × T => C.pathWeight μ p.1 p.2 * (p.1.count i : ℝ))
      ((μ ᵥ* (1 - C.Q)⁻¹) i) := by sorry

end SuttonTD.Convergence
