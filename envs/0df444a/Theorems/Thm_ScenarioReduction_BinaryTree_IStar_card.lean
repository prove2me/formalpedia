-- Prove2me | Theorems.Thm_ScenarioReduction_BinaryTree_IStar_card
-- name    : ScenarioReduction.BinaryTree.IStar_card
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:05:38.509228+00:00
-- url     : https://prove2.me/theorems/93ae5b3b-55f0-4431-bb62-cf0c4c24fe14
-- title:
--   Proof of Proposition 3.1: $\#I_*=N/4$ and $\#J_*=\tfrac34N$
-- statement:
--   Let $K\in\mathbb N$ and $k_0\ge1$ with $k_0+2\le K$, and let $N=2^K$. The set $I_*$ of scenarios of the regular binary tree whose branch at level $k_0$ differs from the branch at level $k_0+1$ and whose branches at levels $k_0+1$ and $k_0+2$ agree, and its complement $J_*=\{1,\dots,N\}\setminus I_*$, have
--
--   $$\#I_*=2^{k_0-1}\cdot2\cdot2^{K-k_0-2}=\tfrac14\,2^K=\tfrac N4,\qquad \#J_*=N-\#I_*=\tfrac34N.$$
--
--   The set $J_*$ is the deleted set that attains the minimal reduction cost when $n=N/4$ scenarios are kept.
--
--   **Formalization Note** $N/4$ and $\frac34N$ are written as $2^{K-2}$ and $3\cdot2^{K-2}$, exact since $K\ge3$. $I_*$ is defined by branch indices rather than by the signs of $\delta^k_{i_k}$ (see the definition `IStar`); the two agree when $\delta^{k_0},\delta^{k_0+1},\delta^{k_0+2}>0$, and the count is a statement about indices only.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 197, proof of Proposition 3.1, display for #I_* and #J_*

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_IStar

namespace ScenarioReduction.BinaryTree

theorem IStar_card (K k0 : ℕ) (hk0 : 1 ≤ k0) (hk0K : k0 + 2 ≤ K) :
    (IStar K k0).card = 2 ^ (K - 2) ∧ (IStar K k0)ᶜ.card = 3 * 2 ^ (K - 2) := by sorry

end ScenarioReduction.BinaryTree
