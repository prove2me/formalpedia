-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_ptLast_swapLast
-- name    : PTCommutant.OperatorBasis.ptLast_swapLast
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:39.94124+00:00
-- url     : https://prove2.me/theorems/24cf35bb-b8f4-4606-82e2-8e6d1bf1e9d8
-- title:
--   p. 9 (with eq. (11), p. 4) — V′(n−1, n) = Φ⁺_{n−1,n}, the unnormalized maximally entangled projector on the last two systems
-- statement:
--   Let $(n\ n-1)$ be the transposition of the last two of $n$ systems of $\mathbb C^d$ and $V'(n\ n-1)$ the partial transpose, on the last system, of its permutation operator. Then
--   $$V'(n-1,n)=\mathbb 1_{1\ldots n-2}\otimes\sum_{l,l'=1}^{d}|ll\rangle\langle l'l'|=\mathbb 1_{1\ldots n-2}\otimes\widetilde\Phi^+_{n-1,n},$$
--   the identity on the first $n-2$ systems tensored with the unnormalized projector onto the maximally entangled vector $\sum_l|ll\rangle$ of systems $n-1,n$. Entrywise: the matrix element between basis strings $x$ and $y$ is $1$ if $x_s=y_s$ for all $s\le n-2$, $x_{n-1}=x_n$ and $y_{n-1}=y_n$, and $0$ otherwise.
--
--   This identifies the only generator of $\mathcal A$ on which the partial transposition acts non-trivially, and it is the operator through which every $v^{ab}_{ij}(\alpha)$ is built.
--
--   **Formalization Note.** $n=m+2$, systems are 0-based, so systems $n-1,n$ are the indices $m$ and $m+1$ and the first $n-2$ systems are the images of `Fin.castLE` from `Fin m`. On p. 9 $\Phi^+$ denotes the unnormalized projector (eq. (11) calls $|\widetilde\Phi^+\rangle$ "unnormalized"); the statement is the unnormalized form, which is $d\cdot\mathbb 1\otimes|\Phi^+\rangle\langle\Phi^+|$ for the normalized $|\Phi^+\rangle$ of Remark 3.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 9 (§IV.A, generators of M: V′(n−1, n) = Φ⁺_{n−1,n}); eq. (11) p. 4

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem ptLast_swapLast {m d : ℕ} (x y : Site d (m + 2)) :
    ptLast (tensorPermutation d (m + 2) (swapLast m)) x y =
      if (∀ i : Fin m, x (Fin.castLE (by omega) i) = y (Fin.castLE (by omega) i)) ∧
          x ⟨m, by omega⟩ = x (Fin.last (m + 1)) ∧ y ⟨m, by omega⟩ = y (Fin.last (m + 1))
        then 1 else 0 := by sorry

end PTCommutant.OperatorBasis
