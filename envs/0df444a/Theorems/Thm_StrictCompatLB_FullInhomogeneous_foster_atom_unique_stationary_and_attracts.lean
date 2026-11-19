-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_foster_atom_unique_stationary_and_attracts
-- name    : StrictCompatLB.FullInhomogeneous.foster_atom_unique_stationary_and_attracts
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T20:07:29.650498+00:00
-- url     : https://prove2.me/theorems/eff3ad18-302d-4e09-80ec-ddd07d91ba4a
-- title:
--   Foster drift plus an accessible aperiodic atom: unique stationary law that attracts the uniformised chain from every state
-- statement:
--   Let $S$ be a countable state space and $K$ a stochastic kernel on $S$. Suppose $V:S\to[0,\infty)$ has summable one-step means $\sum_{z'}K(z,z')V(z')<\infty$, and the Foster drift condition $\sum_{z'}K(z,z')V(z')-V(z)\le -1+b\,\mathbf 1_C(z)$ holds for every $z$, where $C\subseteq S$ is finite and $b\in\mathbb R$. Suppose there is a state $z_0$ with $K(z_0,z_0)>0$ that is reachable with positive probability from every state of $C$, and that $\pi$ is a stationary distribution of $K$. Then $\pi$ is the unique stationary distribution of $K$, and for every rate $r>0$ the uniformised continuous-time chain (jumps at the times of a rate-$r$ Poisson clock, moves by $K$) converges in total variation to $\pi$ from every initial state (AttractsAllStates).
--
--   Role: the ergodicity / interchange-of-limits ingredient of Theorem 3.6 (stationary JSQ(d) occupancy is unique and attracts every state, both for $\lambda>0$ via the Lyapunov function of Lemma H.5 and for $\lambda=0$).
-- source:
--   S. Meyn, R. Tweedie, Markov Chains and Stochastic Stability (2nd ed., 2009), Theorem 11.3.4 (Foster criterion => positive Harris recurrence) and Theorem 13.0.1 (aperiodic ergodic theorem); J. R. Norris, Markov Chains (1997), Theorem 1.8.3 and Section 2.5 (uniformisation); used in D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, proof of Theorem 3.6 (Appendix H)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_CountableChain
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField

namespace StrictCompatLB.FullInhomogeneous

theorem foster_atom_unique_stationary_and_attracts :
    ∀ {S : Type} [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
      (K : S → S → ℝ), IsStochasticKernel K →
      ∀ (V : S → ℝ), (∀ z, 0 ≤ V z) → (∀ z, Summable (fun z' => K z z' * V z')) →
      ∀ (C : Set S), C.Finite → ∀ b : ℝ,
      (∀ z, oneStepDrift K V z ≤ -1 + b * C.indicator (fun _ => (1 : ℝ)) z) →
      ∀ z₀ : S, 0 < K z₀ z₀ → (∀ z ∈ C, ∃ n, 0 < stepProb K n z z₀) →
      ∀ π : S → ℝ, IsStationary K π →
      ∀ rate : ℝ, 0 < rate →
        (∀ π' : S → ℝ, IsStationary K π' → π' = π) ∧ AttractsAllStates K rate π := by sorry

end StrictCompatLB.FullInhomogeneous
