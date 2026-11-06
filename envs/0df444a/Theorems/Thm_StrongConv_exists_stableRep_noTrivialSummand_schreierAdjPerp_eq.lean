-- Prove2me | Theorems.Thm_StrongConv_exists_stableRep_noTrivialSummand_schreierAdjPerp_eq
-- name    : StrongConv.exists_stableRep_noTrivialSummand_schreierAdjPerp_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:56.072931+00:00
-- url     : https://prove2.me/theorems/82f0122b-e832-474b-b6d0-0f587aaa9b59
-- title:
--   Schreier graphs on k-tuples — the restricted adjacency matrix is Σ(Πᵢᴺ + Πᵢᴺ*) for a stable representation with no trivial summand
-- statement:
--   Fix $k \ge 0$. For $\sigma_1, \dots, \sigma_d \in \mathbf S_N$, the Schreier graph of the action of $\mathbf S_N$ on $k$-tuples of distinct elements of $\{1, \dots, N\}$ (`Fin k ↪ Fin N`) joins each tuple $t$ to $\sigma_i \circ t$ for $i = 1, \dots, d$. Its adjacency matrix is $\bar A^N = \sum_i (P_{\sigma_i} + P_{\sigma_i}^*)$ (`schreierAdj k σ`), where $P_\sigma$ (`tuplePermOp k σ`) sends the basis vector $e_t$ to $e_{\sigma\circ t}$. Let $A^N = \bar A^N|_{\{1\}^\perp}$ (`schreierAdjPerp k σ`) be its restriction to the orthogonal complement of the all-ones vector.
--
--   Then there is a stable representation $\pi_N$ of $\mathbf S_N$ (`StableRep`, Definition 3.13), defined for $N \ge N_0$, that contains no copy of the trivial representation (`StableRep.NoTrivialSummand`), with the following property. For every $N \ge N_0$ there is a unitary identification $U : \{1\}^\perp \to \mathbb C^{\dim V_N}$ such that for every $d$, every $\sigma_1, \dots, \sigma_d \in \mathbf S_N$ and every $x \in \{1\}^\perp$,
--   $$U(A^N x) = \Big(\sum_{i=1}^d \big(\Pi^N_i + \Pi^{N*}_i\big)\Big)(Ux), \qquad \Pi^N_i = \pi_N(\sigma_i).$$
--   The representation depends on $k$ only, and $U$ depends on $N$ only, not on $d$ or the $\sigma_i$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 14–15, the representation of random Schreier graphs by a stable representation

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG2

namespace StrongConv

theorem exists_stableRep_noTrivialSummand_schreierAdjPerp_eq (k : ℕ) :
    ∃ π : StableRep, π.NoTrivialSummand ∧ ∀ N : ℕ, π.N₀ ≤ N →
      ∃ U : TupleOnesPerp k N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)),
        ∀ (d : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (x : TupleOnesPerp k N),
          U (schreierAdjPerp k σ x) = (∑ i, (π.model σ i + star (π.model σ i))) (U x) := by
  sorry

end StrongConv
