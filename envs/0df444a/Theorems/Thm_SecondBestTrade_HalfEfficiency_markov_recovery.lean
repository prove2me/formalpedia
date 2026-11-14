-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_markov_recovery
-- name    : SecondBestTrade.HalfEfficiency.markov_recovery
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:47.719408+00:00
-- url     : https://prove2.me/theorems/48329486-efc5-4ac2-b515-78768418943c
-- title:
--   Lemma 5.4 — Markov-chain recovery
-- statement:
--   Fix a useful dual. For each buyer and seller $a$, let $Q_a$ be its constructed generator and let $V_a,\widetilde V_a$ be its true and virtual coordinate matrices. Then $\widetilde V_a=(I-Q_a)V_a$, $I-Q_a$ is invertible, and
--   $$R_a=(I-Q_a)^{-1}=\int_0^\infty e^{-\theta}e^{\theta Q_a}\,d\theta.$$
--   The matrices $e^{\theta Q_a}$ form a continuous stochastic semigroup and are the transition matrices of a finite-state continuous-time Markov chain from each initial support type. Every row is a probability distribution. Stopping independently at a rate-one exponential time gives row $R_a(t,\cdot)$ as the terminal law. For every incident coordinate $e$,
--   $$\mathbb E[\widetilde V_a(\widehat t,e)\mid t]=\sum_s R_a(t,s)\widetilde V_a(s,e)=V_a(t,e).$$
--   The resolvent entries and exponential-weighted virtual-coordinate expectations are integrable. The conclusion applies to every buyer and every seller, with the same generator acting on all coordinates of an agent.
--
--   This recovers entire multidimensional types and includes the chain and terminal-law interpretation as well as the algebraic identity.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: matrix integral, independently exponentially stopped chain, and vector recovery using (5.8) → entrywise integrable density integrals, finite-dimensional chain laws on a probability space, stochastic continuous semigroup, and coordinatewise recovery with zero extension outside incident trades; reason: rate-one stopping has density exp(-theta); finite coordinates give the same integral, law and vector identities; (5.8) is written explicitly and no recovery is assumed
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma 5.4 — Markov-chain recovery, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Recovery

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma 5.4, printed p. 10 (PDF p. 11), with both sides and every coordinate. -/
theorem markov_recovery (N : Market) (z : Dual N) (hz : useful N z) :
    ∀ a : Agent N,
      (∀ t e, virtual N z a t e = ∑ s,
        (1 - generator N z a) t s * coord N a s e) ∧
      recoveryProperties (generator N z a) (coord N a) (virtual N z a) := by sorry

end SecondBestTrade.HalfEfficiency
