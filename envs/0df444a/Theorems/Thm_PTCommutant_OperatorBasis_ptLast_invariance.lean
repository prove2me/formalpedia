-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_ptLast_invariance
-- name    : PTCommutant.OperatorBasis.ptLast_invariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:24.572025+00:00
-- url     : https://prove2.me/theorems/70efa7c8-ba89-4d3d-ab7b-c367e2b0e4db
-- title:
--   Proof of Lemma 26, p. 17 — permutations of S(n−1) are invariant under the partial transposition ′ over the last subsystem
-- statement:
--   Let $V(\tau)$ denote the permutation operator of $\tau\in S(n)$ on $(\mathbb C^d)^{\otimes n}$, and let $X'$ be the partial transpose of $X$ on the last system. Regard $S(n-1)$ as the permutations of $S(n)$ fixing the last system. Then for all $\rho,\rho'\in S(n-1)$ and $\tau\in S(n)$:
--
--   1. permutation operators of $S(n-1)$ are invariant under partial transposition,
--   $$V'(\rho)=V(\rho);$$
--   2. they pass through the partial transposition,
--   $$V(\rho)\,V'(\tau)\,V(\rho')=V'(\rho\circ\tau\circ\rho').$$
--
--   This is the fact used in the proof of Lemma 26 to rewrite $\Pi_b V(f_{ab}^{-1}(\sigma_{ab}))V'(n\ n-1)\Pi_a^{-1}$ as $V'(\pi_b\circ f^{-1}_{ab}(\sigma_{ab})\circ(n\ n-1)\circ\pi_a^{-1})$ (eq. (82)); it is what makes $\mathcal A$ invariant under left and right multiplication by $S(n-1)$.
--
--   **Formalization Note.** The paper's $n$ is $k+2$ here; $S(n-1)$ embeds into $S(n)$ by `liftPerm (k+1) 1`. Statement (2) is the general form of the step in eq. (82); the case of eq. (82) is $\rho=\pi_b\circ f^{-1}_{ab}(\sigma_{ab})$, $\tau=(n\ n-1)$, $\rho'=\pi_a^{-1}$.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 17, proof of Lemma 26 (eq. (82))

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem ptLast_invariance {d k : ℕ} (ρ ρ' : Equiv.Perm (Fin (k + 1)))
    (τ : Equiv.Perm (Fin (k + 2))) :
    ptLast (tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ)) =
        tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ) ∧
      tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ) *
          ptLast (tensorPermutation d (k + 2) τ) *
          tensorPermutation d (k + 2) (liftPerm (k + 1) 1 ρ') =
        ptLast (tensorPermutation d (k + 2)
          (liftPerm (k + 1) 1 ρ * τ * liftPerm (k + 1) 1 ρ')) := by sorry

end PTCommutant.OperatorBasis
