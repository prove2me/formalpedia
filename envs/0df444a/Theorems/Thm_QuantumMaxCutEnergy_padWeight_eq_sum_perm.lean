-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_padWeight_eq_sum_perm
-- name    : QuantumMaxCutEnergy.padWeight_eq_sum_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:17:55.876951+00:00
-- url     : https://prove2.me/theorems/bec91abf-d7df-4fb8-bbfb-f504e4c2ee3d
-- title:
--   Birkhoff: the padded fractional matching is a convex combination of permutation matrices
-- statement:
--   **Birkhoff: the padded edge weight is a convex combination of permutation matrices.**
--
--   If $x\ge0$ is an edge weight on a graph on $n$ vertices with vertex loads at most $1$, then there are weights
--   $\lambda_\sigma\ge0$ on the permutations $\sigma$ of the $n$ vertices with $\sum_\sigma\lambda_\sigma=1$ and
--   $$\sum_\sigma \lambda_\sigma\,P_\sigma \;=\; \mathrm{padWeight}\,x ,$$
--   where $P_\sigma$ is the permutation matrix of $\sigma$.
--
--   **Proof.** This is Birkhoff–von Neumann's theorem, in Mathlib's form
--   `exists_eq_sum_perm_of_mem_doublyStochastic`: a doubly stochastic matrix is a convex combination of permutation
--   matrices. The hypothesis that $\mathrm{padWeight}\,x$ is doubly stochastic is the previous node
--   (`QuantumMaxCutEnergy.padWeight_mem_doublyStochastic`, imported — this submission is a tracked reduction).
--
--   **Role.** In the bipartite case of Edmonds' exactness, every off-diagonal entry of $\mathrm{padWeight}\,x$ joins
--   the two colour classes. So in a permutation with $\lambda_\sigma>0$ every non-fixed step crosses the
--   bipartition, the cycles are therefore even and alternate between the classes, and the two alternating
--   matchings of a cycle partition its edges — one of them carries at least half the cycle's weight. That converts
--   the decomposition into an integral matching of weight at least $\sum_e w_ex_e$: the last step of the bipartite
--   warm-up, still to be formalized.
-- source:
--   Birkhoff, L'Enseignement Math. 34 (1946); von Neumann (1953); Mathlib's `exists_eq_sum_perm_of_mem_doublyStochastic`.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

theorem padWeight_eq_sum_perm {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) :
    ∃ lam : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ lam σ) ∧ (∑ σ, lam σ = 1) ∧
      ∑ σ, lam σ • Equiv.Perm.permMatrix ℝ σ = padWeight x := by sorry

end QuantumMaxCutEnergy
