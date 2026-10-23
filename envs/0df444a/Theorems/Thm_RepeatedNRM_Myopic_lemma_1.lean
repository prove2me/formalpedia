-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_lemma_1
-- name    : RepeatedNRM.Myopic.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:10.107857+00:00
-- url     : https://prove2.me/theorems/87016005-4e87-4ed3-b5fa-abb3af51ccf1
-- title:
--   Lemma 1, p. ec2 — MY(b) is monotone in the budget vector
-- statement:
--   Let $\mathrm{MY}(\mathbf b)$ be the optimal value of the myopic linear program (7), the largest revenue $\sum_{i,j}p_{ij}x_{ij}$ over allocations $x\in X(\mathbf b)$ that respect the budget constraints $\sum_i p_{ij}x_{ij}\le b_j$ and the supplies $\sum_j x_{ij}\le s_i$.
--
--   For budget vectors $\mathbf b,\bar{\mathbf b}\in[0,1]^m$ with $\bar b_j\ge b_j$ for every customer $j$,
--   $$\mathrm{MY}(\bar{\mathbf b})\ \ge\ \mathrm{MY}(\mathbf b).$$
--
--   Larger budgets only enlarge the feasible set of (7). The lemma is used in Proposition 2 and Corollary 1.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - encoding: $\mathrm{MY}(\mathbf b)=\max_{x\in X(\mathbf b)}R(x)$ → the supremum of $R$ over $X(\mathbf b)$; reason: the set is nonempty, compact and $R$ is continuous, so the supremum is the maximum
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. ec2, Lemma 1

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

theorem lemma_1 (I : Instance) (hI : I.Standing) (b bbar : Fin I.m → ℝ)
    (hb : ∀ j, b j ∈ Set.Icc (0 : ℝ) 1) (hbbar : ∀ j, bbar j ∈ Set.Icc (0 : ℝ) 1)
    (hle : ∀ j, b j ≤ bbar j) :
    MY I b ≤ MY I bbar := by sorry
end RepeatedNRM.Myopic
