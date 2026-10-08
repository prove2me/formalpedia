-- Prove2me | Theorems.Thm_SennottDP_ChainASM_as_taboo_visits_passage_limits
-- name    : SennottDP.ChainASM.as_taboo_visits_passage_limits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T14:30:23.896837+00:00
-- url     : https://prove2.me/theorems/e8274a16-6aee-4b9c-ac0f-81dfcc5f8967
-- title:
--   Proposition C.4.2 — taboo probabilities converge; expected visits and first passage times are lower semicontinuous along an AS
-- statement:
--   Let $\Gamma$ be a Markov chain with costs on a denumerable state space $S$, let $(\Gamma_N)$ be an approximating sequence for $\Gamma$, and let $G$ be a finite nonempty subset of $S$. Then:
--
--   1. $\lim_{N\to\infty}{}_GP^{(t)}_{ik}(N)={}_GP^{(t)}_{ik}$ for $i,k\in S$ and $t\ge 1$;
--   2. ${}_Gu_{ik}(N)={}_Gu_{ik}=\delta_{ik}$ for $k\in G$, $i\in S$ and $N$ sufficiently large; in general
--   $$\liminf_{N\to\infty}{}_Gu_{ik}(N)\ge{}_Gu_{ik},\qquad i,k\in S;$$
--   3. $\liminf_{N\to\infty}m_{iG}(N)\ge m_{iG}$ for $i\in S$.
--
--   Taboo probabilities over a fixed number of steps converge, while expected visit counts and first passage times, which are infinite sums of them, can only lose mass in the limit. These inequalities are the starting point of every convergence argument for approximating sequences in the book.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 303, Proposition C.4.2

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_taboo_visits_passage_limits {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (G : Finset S) (hG : G.Nonempty) :
    (∀ i k : S, ∀ t : ℕ, 1 ≤ t →
      Tendsto (fun N => AS.tabooProbN (↑G : Set S) t N i k) atTop
        (𝓝 (Γ.tabooProb (↑G : Set S) t i k))) ∧
    (∀ k ∈ G, ∀ i : S, Γ.visits (↑G : Set S) i k = (if i = k then 1 else 0) ∧
      ∀ᶠ N in atTop, AS.visitsN (↑G : Set S) N i k = Γ.visits (↑G : Set S) i k) ∧
    (∀ i k : S, Γ.visits (↑G : Set S) i k ≤
      liminf (fun N => AS.visitsN (↑G : Set S) N i k) atTop) ∧
    (∀ i : S, Γ.meanPassage (↑G : Set S) i ≤
      liminf (fun N => AS.meanPassageN (↑G : Set S) N i) atTop) := by sorry

end SennottDP.ChainASM
