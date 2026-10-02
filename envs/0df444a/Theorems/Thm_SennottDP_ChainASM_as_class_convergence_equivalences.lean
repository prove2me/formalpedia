-- Prove2me | Theorems.Thm_SennottDP_ChainASM_as_class_convergence_equivalences
-- name    : SennottDP.ChainASM.as_class_convergence_equivalences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:47:14.458495+00:00
-- url     : https://prove2.me/theorems/fba2c8e2-4405-426e-9a44-4c593144fca3
-- title:
--   Proposition C.4.6 — on a positive recurrent class, convergence of π, of m_zz and of m_iG are equivalent, and then so are those of J, c_zz and c_iG
-- statement:
--   Let $(\Gamma_N)$ be an approximating sequence for the Markov chain with costs $\Gamma$ on a denumerable state space $S$, and let $R$ be a positive recurrent class of $\Gamma$. Then the following are equivalent:
--
--   1. $\pi_i(N)\to\pi_i$ for $i\in R$;
--   2. $m_{zz}(N)\to m_{zz}$ for some $z\in R$;
--   3. $m_{iG}(N)\to m_{iG}$ for any nonempty finite subset $G$ of $R$ and $i\in R$.
--
--   Assume that any (and hence all) of these hold. Then the following are equivalent:
--
--   4. $J(i)(N)\to J_R$ for $i\in R$;
--   5. $c_{zz}(N)\to c_{zz}$ for some $z\in R$;
--   6. $c_{iG}(N)\to c_{iG}$ for any nonempty finite subset $G$ of $R$ and $i\in R$.
--
--   Here $J_R=\sum_{j\in R}\pi_jC(j)$ is the (possibly infinite) average cost on $R$. The result reduces convergence of steady state probabilities and average costs on a class to convergence of the first passage moments to a single state.
--
--   **Formalization Note** All limits are in $[0,\infty]$; the equivalences are stated with `List.TFAE`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 305, Proposition C.4.6

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_class_convergence_equivalences {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (R : Set S) (hR : Γ.IsPosRecClass R) :
    List.TFAE
      [∀ i ∈ R, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i)),
       ∃ z ∈ R, Tendsto (fun N => AS.meanPassageN {z} N z) atTop
         (𝓝 (Γ.meanPassage {z} z)),
       ∀ G : Finset S, G.Nonempty → (↑G : Set S) ⊆ R → ∀ i ∈ R,
         Tendsto (fun N => AS.meanPassageN (↑G : Set S) N i) atTop
           (𝓝 (Γ.meanPassage (↑G : Set S) i))] ∧
    ((∀ i ∈ R, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i))) →
      List.TFAE
        [∀ i ∈ R, Tendsto (fun N => AS.avgCostN N i) atTop (𝓝 (Γ.classAvgCost R)),
         ∃ z ∈ R, Tendsto (fun N => AS.passageCostN {z} N z) atTop
           (𝓝 (Γ.passageCost {z} z)),
         ∀ G : Finset S, G.Nonempty → (↑G : Set S) ⊆ R → ∀ i ∈ R,
           Tendsto (fun N => AS.passageCostN (↑G : Set S) N i) atTop
             (𝓝 (Γ.passageCost (↑G : Set S) i))]) := by sorry

end SennottDP.ChainASM
