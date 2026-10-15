-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_2
-- name    : StrictCompatLB.RegularDegree.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:24.044174+00:00
-- url     : https://prove2.me/theorems/8f3f05df-998e-44cf-bed0-461a28bd32da
-- title:
--   Lemma A.2 — a.s. eventually, for every large dispatcher set X, at most δN servers have an atypical number of neighbours in X
-- statement:
--   Let $c(N)\le M(N)$ be positive integers, and let $G_N$ be the random compatibility graph of Theorem 3.5: each server $v\in V_N$ chooses its neighbourhood $\mathcal N_v$ uniformly among the $c(N)$-subsets of the $M(N)$ dispatchers, independently over servers, with no assumption on the joint law across $N$. For $\varepsilon>0$ and $X\subseteq W_N$ let
--   $$B_N(X)=\Big\{v\in V_N:\Big||\mathcal N_v\cap X|-\frac{c(N)|X|}{M(N)}\Big|\ge\frac{\varepsilon\,c(N)|X|}{M(N)}\Big\}.$$
--   Assume $c(N)\to\infty$ and $Nc(N)/M(N)\to\infty$. Then for all $0<\varepsilon\le 3/2$, $0<\delta<1/2$ and $\eta>0$, almost surely there exists $N_0\ge 1$ such that for all $N\ge N_0$ and all $X\subseteq W_N$ with $|X|\ge\eta M(N)$,
--   $$|B_N(X)|\le\delta N .$$
--
--   The null set may depend on $\varepsilon,\delta,\eta$ but not on $X$: the almost-sure event is uniform over all large dispatcher sets. This is the concentration statement behind both Lemma A.3 and Proposition A.4.
--
--   **Formalization Note** $c(N)=\omega(1)$ and $c(N)=\omega(M(N)/N)$ are written as real limits $c(N)\to\infty$ and $Nc(N)/M(N)\to\infty$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 31, Lemma A.2, (A.3)

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree

theorem lemma_A_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 3 / 2) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (η : ℝ) (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ X : Finset (Fin (M N)),
      η * (M N : ℝ) ≤ (X.card : ℝ) →
        ((badServers M c (randomGraph M adj ω) ε N X).card : ℝ) ≤ δ * (N : ℝ) := by sorry

end StrictCompatLB.RegularDegree
