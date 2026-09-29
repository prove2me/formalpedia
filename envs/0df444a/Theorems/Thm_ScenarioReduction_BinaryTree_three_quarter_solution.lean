-- Prove2me | Theorems.Thm_ScenarioReduction_BinaryTree_three_quarter_solution
-- name    : ScenarioReduction.BinaryTree.three_quarter_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:06:53.935502+00:00
-- url     : https://prove2.me/theorems/30f1c18c-0713-4330-8b9b-c4a73ffdfe3e
-- title:
--   Proposition 3.1 (3/4-solution): $D^{min}_n=\frac{N-n}{N}2\delta^{k_0}$ for $\frac N4\le n<N$ on a regular binary tree
-- statement:
--   Let a regular binary scenario tree with $N=2^K$ scenarios $\omega_1,\dots,\omega_N\in\mathbb R^{K+1}$ and $K\ge3$ be given: $\omega_i^k=\sum_{j=0}^k\delta^j_{i_j}$ with $\delta^j_{i_j}=\pm\delta^j$, level parameters $\delta^1,\dots,\delta^K\ge0$, and probabilities $p_i=1/N$. Distances are measured in the maximum norm, $\|\omega-\tilde\omega\|_\infty=\max_{k=0,\dots,K}|\omega^k-\tilde\omega^k|$, and $D_J=\sum_{i\in J}p_i\min_{j\notin J}\|\omega_i-\omega_j\|_\infty$ is the cost of deleting the scenarios in $J$. Let
--
--   $$k_0\in\arg\min_{1\le k\le K}\delta^k,\qquad k_0\le K-2,\qquad \max\{\delta^{k_0+1},\delta^{k_0+2}\}\le2\delta^{k_0}.$$
--
--   Then:
--
--   1. the distance between any two distinct scenarios is not smaller than $2\delta^{k_0}$;
--   2. there are (at least) $\frac34N$ distinct pairs of scenarios whose members are at distance exactly $2\delta^{k_0}$: there is a set $J_*$ of $\frac34N$ scenarios such that every $j\in J_*$ has a partner $i\notin J_*$ with $\|\omega_i-\omega_j\|_\infty=2\delta^{k_0}$;
--   3. for each $n\in\mathbb N$ with $\frac N4\le n<N$, the minimum of $D_J$ over all $J$ with $\#J=N-n$ exists and equals
--
--   $$D^{min}_n:=\min\{D_J:\#J=N-n\}=\frac{N-n}{N}\,2\delta^{k_0}.\tag{20}$$
--
--   Proposition 3.1 gives the exact optimal value of the NP-hard optimal scenario reduction problem (8) for an explicit family of scenario trees, and is used in Section 4 of the paper as a benchmark against which the heuristic reduction algorithms are measured.
--
--   **Formalization Note** Scenarios are indexed by `Fin K → Fin 2` (Fin-index $r$ is tree level $r+1$), so there are exactly $2^K$ of them; the parameters are $\delta:\mathbb N\to\mathbb R$, with nonnegativity and the arg min stated over $k=1,\dots,K$. The minimum in (20) is stated as `IsLeast` of the set of attained values $D_J$, so it includes attainment. $\frac34N$ is $3\cdot2^{K-2}$, and $\frac N4\le n$ is $2^K\le4n$. "Any scenarios" in claim 1 means two distinct scenarios, as in the proof. Claim 2 is stated as "at least $\frac34N$ pairs", in the form the proof exhibits: read as an exact count the printed claim is false (for $K=3$, $\delta=(1,1,1)$, $k_0=1$, twenty unordered pairs are at distance exactly $2$, while $\frac34N=6$). The pairs $(j,i(j))$, $j\in J_*$, are pairwise distinct because each contains exactly one member of $J_*$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 196, Proposition 3.1, eq. (20)

import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_redCost

namespace ScenarioReduction.BinaryTree

theorem three_quarter_solution (K : ℕ) (δ : ℕ → ℝ) (hδ : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ k)
    (hK : 3 ≤ K) (k0 : ℕ) (hk0 : k0 ∈ Finset.Icc 1 K)
    (hmin : ∀ k ∈ Finset.Icc 1 K, δ k0 ≤ δ k) (hk0K : k0 ≤ K - 2)
    (hmax : max (δ (k0 + 1)) (δ (k0 + 2)) ≤ 2 * δ k0) :
    (∀ σ τ : Fin K → Fin 2, σ ≠ τ → 2 * δ k0 ≤ ‖scenario δ σ - scenario δ τ‖) ∧
    (∃ Jstar : Finset (Fin K → Fin 2), Jstar.card = 3 * 2 ^ (K - 2) ∧
      ∀ j ∈ Jstar, ∃ i ∉ Jstar, ‖scenario δ i - scenario δ j‖ = 2 * δ k0) ∧
    (∀ n : ℕ, 2 ^ K ≤ 4 * n → n < 2 ^ K →
      IsLeast {v : ℝ | ∃ J : Finset (Fin K → Fin 2), J.card = 2 ^ K - n ∧
          ∃ hJ : Jᶜ.Nonempty, v = redCost δ J hJ}
        (((2 : ℝ) ^ K - n) / 2 ^ K * (2 * δ k0))) := by sorry

end ScenarioReduction.BinaryTree
