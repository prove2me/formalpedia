-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_eq_21
-- name    : PTCommutant.OperatorBasis.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:37.152457+00:00
-- url     : https://prove2.me/theorems/41951671-7990-4305-8fdf-149200aadcc1
-- title:
--   Eq. (21) with Definition 2, p. 6 — E^α_{ij} ∈ C[S(n−2)] maps to v^{ab}_{ij}(α) ∈ M under F^t_ba
-- statement:
--   Let $\varphi^\alpha$ be real orthogonal, irreducible, pairwise inequivalent irreps of $S(n-2)$ with an adapted orthonormal Schur basis $|\phi_i(\alpha,r)\rangle$ of $(\mathbb C^d)^{\otimes(n-2)}$, let $\pi_k\in S(n-1)$ with $\pi_k(n-1)=k$ and $\Pi_k=V(\pi_k)$. Let $E^\alpha_{ij}=\sum_r|\phi_i(\alpha,r)\rangle\langle\phi_j(\alpha,r)|$ (footnote 4) and $v^{ab}_{ij}(\alpha)=\sum_r|\psi^a_i(\alpha,r)\rangle\langle\psi^b_j(\alpha,r)|$ with $|\psi^k_i(\alpha,r)\rangle=\sqrt d\,V(\pi_k)|\phi_i(\alpha,r)\rangle|\Phi^+\rangle$ (Definitions 4, 5). With the map $\mathcal F^t_{ab}(X)=\Pi_b\,X\,V'(n\ n-1)\,\Pi_a^{-1}$ of Definition 2, for all $a,b\in\{1,\dots,n-1\}$, labels $\alpha$ and $i,j$:
--   $$E^\alpha_{ij}\in\mathbb C[S(n-2)],\qquad v^{ab}_{ij}(\alpha)=\mathcal F^t_{ba}\big(E^\alpha_{ij}\big)=\Pi_a\,\big(E^\alpha_{ij}\otimes\mathbb 1_{n-1,n}\big)\,V'(n\ n-1)\,\Pi_b^{-1}\in\mathcal M.$$
--
--   This is the statement $\mathbb C[S(n-2)]\ni E^\alpha_{ij}\overset{\mathcal F^t_{ba}}{\longmapsto}v^{ab}_{ij}(\alpha)$ of eq. (21): the operator basis of §III.C is the image of the matrix units of the group algebra under the maps of Definition 2.
--
--   **Formalization Note.** $n=m+2$, labels are `Fin (m+1)`. The represented group algebra and the ideal $\mathcal M$ are `groupAlg` and `algM`; $X\otimes\mathbb 1_{n-1,n}$ is `embedOp X`. $v^{ab}_{ij}(\alpha)$ is built from Definition 5, never from $\mathcal F^t_{ba}$, so the identity has content. The standing hypothesis $\pi_k(n-1)=k$ is carried although this identity does not need it.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 6, eq. (21) and footnote 4; Definition 2 (eq. (12)) p. 5; Definitions 4–5 p. 5

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem eq_21 {m d : ℕ} (F : IrrepFamily m) (B : SchurBasis F d)
    (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1))) (hπ : ∀ k, π k (Fin.last m) = k)
    (a b : Fin (m + 1)) (α : F.ι) (i j : Fin (F.dim α)) :
    EOp B α i j ∈ groupAlg d m ∧
      vOp B π a b α i j =
        tensorPermutation d (m + 2) (liftPerm (m + 1) 1 (π a)) * embedOp (EOp B α i j) *
          ptLast (tensorPermutation d (m + 2) (swapLast m)) *
          tensorPermutation d (m + 2) ((liftPerm (m + 1) 1 (π b))⁻¹) ∧
      vOp B π a b α i j ∈ algM d m := by sorry

end PTCommutant.OperatorBasis
