-- Prove2me | Theorems.Thm_ScenarioReduction_BinaryTree_redCost_lower_bound
-- name    : ScenarioReduction.BinaryTree.redCost_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:04:49.29576+00:00
-- url     : https://prove2.me/theorems/392698a1-5d41-4a6a-a5df-ddf1fbb426ff
-- title:
--   Proof of Proposition 3.1: $D_J\ge\frac{N-n}{N}2\delta^{k_0}$ for every $J$ with $\#J=N-n$
-- statement:
--   Let a regular binary scenario tree with $N=2^K$ scenarios, probabilities $p_i=1/N$ and level parameters $\delta^1,\dots,\delta^K\ge0$ be given, and let $k_0\in\arg\min_{1\le k\le K}\delta^k$. Let $n\in\mathbb N$ with $n<N$. Then for every set $J\subset\{1,\dots,N\}$ of deleted scenarios with $\#J=N-n$,
--
--   $$D_J=\sum_{i\in J}p_i\min_{j\notin J}\|\omega_i-\omega_j\|_\infty\ \ge\ \sum_{i\in J}\frac1N\,2\delta^{k_0}=\frac{N-n}{N}\,2\delta^{k_0}.$$
--
--   This is the lower-bound half of eq. (20): no reduced tree with $n$ scenarios is closer to the original tree than $\frac{N-n}{N}2\delta^{k_0}$.
--
--   **Formalization Note** The complement of $J$ is nonempty (argument `hJ`, automatic when $n\ge1$), as `redCost` requires. $N-n$ is computed in $\mathbb N$ under $n<2^K$ in the cardinality constraint and in $\mathbb R$ in the bound.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 197, proof of Proposition 3.1, first display

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_redCost

namespace ScenarioReduction.BinaryTree

theorem redCost_lower_bound (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K) (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k)
    (n : ℕ) (hn : n < 2 ^ K) (J : Finset (Fin K → Fin 2)) (hJcard : J.card = 2 ^ K - n)
    (hJ : Jᶜ.Nonempty) :
    ((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0) ≤ redCost δ J hJ := by sorry

end ScenarioReduction.BinaryTree
