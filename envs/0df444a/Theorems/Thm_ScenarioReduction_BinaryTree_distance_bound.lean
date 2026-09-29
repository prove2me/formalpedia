-- Prove2me | Theorems.Thm_ScenarioReduction_BinaryTree_distance_bound
-- name    : ScenarioReduction.BinaryTree.distance_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:04:06.963402+00:00
-- url     : https://prove2.me/theorems/fac48a39-7592-4c58-a1de-38dfb5f65ce2
-- title:
--   Proof of Proposition 3.1: two scenarios first differing at level $l$ are at distance $\ge 2\delta^l\ge2\delta^{k_0}$
-- statement:
--   Let a regular binary scenario tree with $N=2^K$ scenarios $\omega_1,\dots,\omega_N$ be given, with level parameters $\delta^1,\dots,\delta^K\ge0$, and let $k_0\in\arg\min_{1\le k\le K}\delta^k$. Let $i,j$ be two scenarios with branch indices $(i_1,\dots,i_K)$ and $(j_1,\dots,j_K)$, and let $l\in\{1,\dots,K\}$ be the first level at which they differ: $i_l\neq j_l$ and $i_r=j_r$ for $r=1,\dots,l-1$. Then
--
--   $$\|\omega_i-\omega_j\|_\infty\ \ge\ 2\delta^{l}\ \ge\ 2\delta^{k_0}.$$
--
--   Since any two distinct scenarios have a first level of disagreement, the distance between any two distinct scenarios is at least $2\delta^{k_0}$; this is the first assertion of Proposition 3.1 and the source of the lower bound on $D_J$.
--
--   **Formalization Note** Scenarios are indexed by `σ τ : Fin K → Fin 2` and the branch at level $k$ is `lev σ k`; the norm is Mathlib's sup norm on `Fin (K+1) → ℝ`. The hypotheses "$\delta^k\in\mathbb R_+$" and "$k_0\in\arg\min$" are stated for the levels $1,\dots,K$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 196, proof of Proposition 3.1, last display

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario

namespace ScenarioReduction.BinaryTree

theorem distance_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (σ τ : Fin K → Fin 2) (l : ℕ) (hl : l ∈ Finset.Icc 1 K) (hdiff : lev σ l ≠ lev τ l)
    (hagree : ∀ r ∈ Finset.Icc 1 (l - 1), lev σ r = lev τ r) :
    2 * δ l ≤ ‖scenario δ σ - scenario δ τ‖ ∧ 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖ := by sorry

end ScenarioReduction.BinaryTree
