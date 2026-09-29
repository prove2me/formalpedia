-- Prove2me | Theorems.Thm_ScenarioReduction_BinaryTree_partner_exists
-- name    : ScenarioReduction.BinaryTree.partner_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:06:20.389527+00:00
-- url     : https://prove2.me/theorems/97d9f9ea-586c-4338-a251-ce8f8d6a2b1a
-- title:
--   Proof of Proposition 3.1: every $j\in J_*$ has a partner $i\in I_*$ with $\|\omega_i-\omega_j\|_\infty=2\delta^{k_0}$
-- statement:
--   Let a regular binary scenario tree with $N=2^K$ scenarios and $K\ge3$ be given, with level parameters $\delta^1,\dots,\delta^K\ge0$. Let $k_0\in\arg\min_{1\le k\le K}\delta^k$ with $k_0\le K-2$ and
--
--   $$\max\{\delta^{k_0+1},\delta^{k_0+2}\}\le 2\delta^{k_0}.$$
--
--   Let $I_*$ be the set of scenarios with $i_{k_0}\ne i_{k_0+1}=i_{k_0+2}$ and $J_*$ its complement. Then for every $j\in J_*$ there is an $i\in I_*$ with
--
--   $$\|\omega_i-\omega_j\|_\infty=2\delta^{k_0}.$$
--
--   Together with the lower bound on the pairwise distances this shows that deleting exactly the scenarios of $J_*$ costs $D_{J_*}=\frac{\#J_*}{N}2\delta^{k_0}=\frac32\delta^{k_0}$, so the lower bound of Proposition 3.1 is attained for $n=N/4$.
--
--   **Formalization Note** The hypotheses are exactly those of Proposition 3.1, with $\delta^k\in\mathbb R_+$ stated for $k=1,\dots,K$. $I_*$ is the index-defined set `IStar K k0` (it agrees with the paper's sign definition when the three parameters at levels $k_0,k_0+1,k_0+2$ are positive).
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), pp. 197–198, proof of Proposition 3.1, cases (1)–(3) and the following display

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_IStar

namespace ScenarioReduction.BinaryTree

theorem partner_exists (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    ∀ j ∉ IStar K k0, ∃ i ∈ IStar K k0, ‖scenario δ i - scenario δ j‖ = 2 * δ k0 := by sorry

end ScenarioReduction.BinaryTree
