-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_theorem_9
-- name    : PTCommutant.OperatorBasis.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:26.384364+00:00
-- url     : https://prove2.me/theorems/26027e53-5dc9-426a-a38d-7e645944dd53
-- title:
--   Theorem 9, p. 6 — v^{ab}_{ij}(α) = (d_α/(n−2)!) Σ φ^α_{ij}(σ) V′(f_ba(σ)) ∈ A, and V′(σ_ab) = Σ_α Σ_ij φ^α_{ij}(f_ab⁻¹(σ_ab)) v^{ba}_{ij}(α)
-- statement:
--   Let $n\ge2$ and $d\ge0$. Let $\varphi^\alpha$ be a finite family of real orthogonal matrix representations of $S(n-2)$, of dimensions $d_\alpha\ge1$, irreducible and pairwise inequivalent over $\mathbb C$, and let $|\phi_i(\alpha,r)\rangle$ be an orthonormal basis of $(\mathbb C^d)^{\otimes(n-2)}$ with $V(\sigma)|\phi_j(\alpha,r)\rangle=\sum_i\varphi^\alpha_{ij}(\sigma)|\phi_i(\alpha,r)\rangle$. Fix $\pi_1,\dots,\pi_{n-1}\in S(n-1)$ with $\pi_k(n-1)=k$, put $f_{ab}(\sigma)=\pi_b\circ\sigma\circ(n\ n-1)\circ\pi_a^{-1}$ (eq. (7)), and define
--   $$|\psi^k_i(\alpha,r)\rangle=\sqrt d\,V(\pi_k)|\phi_i(\alpha,r)\rangle|\Phi^+\rangle,\qquad v^{ab}_{ij}(\alpha)=\sum_r|\psi^a_i(\alpha,r)\rangle\langle\psi^b_j(\alpha,r)|,$$
--   with $|\Phi^+\rangle=\frac1{\sqrt d}\sum_l|ll\rangle$ on the last two systems. Let $X'$ be the partial transpose on the last system and $\mathcal A=\operatorname{span}_{\mathbb C}\{V'(\tau):\tau\in S(n)\}$. Then for all $a,b\in\{1,\dots,n-1\}$, labels $\alpha$ and indices $i,j$:
--
--   (a) the operator basis is a combination of partially transposed permutation operators,
--   $$v^{ab}_{ij}(\alpha)=\frac{d_\alpha}{(n-2)!}\sum_{\sigma\in S(n-2)}\varphi^\alpha_{ij}(\sigma)\,V'\big(f_{ba}(\sigma)\big),\qquad f_{ba}(\sigma)=\pi_a\circ\sigma\circ(n\ n-1)\circ\pi_b^{-1},$$
--   and in particular $v^{ab}_{ij}(\alpha)\in\mathcal A$;
--
--   (b) conversely, for every $\sigma\in S(n-2)$ and $\sigma_{ab}=f_{ab}(\sigma)$, so that $f^{-1}_{ab}(\sigma_{ab})=\sigma$,
--   $$V'(\sigma_{ab})=\bigoplus_\alpha\sum_{i,j}\varphi^\alpha_{ij}\big(f^{-1}_{ab}(\sigma_{ab})\big)\,v^{ba}_{ij}(\alpha).$$
--
--   By eq. (9), every $\tau\in S(n)$ with $\tau(n)\ne n$ is $f_{ab}(\sigma)$ for exactly one $(a,b,\sigma)$, so (b) covers every partially transposed permutation operator outside $\mathbb C[S(n-1)]$. The theorem is the paper's main result: it shows that the $v^{ab}_{ij}(\alpha)$ and the $V'(\sigma_{ab})$ span the same space, which is the starting point for the irreducible representations of $\mathcal A$ constructed in the rest of the paper.
--
--   **Formalization Note.** The paper's $n$ is $m+2$; $S(n-2)=$ `Equiv.Perm (Fin m)`, labels $a,b$ are `Fin (m+1)` (0-based), $d_\alpha=$ `F.dim α`, $(n-2)!=$ `m.factorial`, `fPerm π b a` is $f_{ba}$. The irreps and the Schur basis are standing data of the paper (taken as given there) and enter as the hypotheses `F : IrrepFamily m` and `B : SchurBasis F d`; they include irreducibility and inequivalence, without which (a) and (b) fail. $\bigoplus_\alpha$ is the sum over all labels. Part (b) is parametrised by $\sigma\in S(n-2)$ through $\sigma_{ab}=f_{ab}(\sigma)$, the paper's own parametrisation of eq. (7).
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 6, Theorem 9 (eqs. (22), (23)); restated p. 17 (eqs. (84), (85))

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem theorem_9 {m d : ℕ} (F : IrrepFamily m) (B : SchurBasis F d)
    (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1))) (hπ : ∀ k, π k (Fin.last m) = k) :
    (∀ (a b : Fin (m + 1)) (α : F.ι) (i j : Fin (F.dim α)),
      vOp B π a b α i j =
        ((F.dim α : ℂ) / (m.factorial : ℂ)) •
          ∑ σ : Equiv.Perm (Fin m), ((F.rep α σ i j : ℝ) : ℂ) •
            ptLast (tensorPermutation d (m + 2) (fPerm π b a σ))) ∧
    (∀ (a b : Fin (m + 1)) (α : F.ι) (i j : Fin (F.dim α)), vOp B π a b α i j ∈ algA d m) ∧
    (∀ (a b : Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      ptLast (tensorPermutation d (m + 2) (fPerm π a b σ)) =
        ∑ α : F.ι, ∑ i : Fin (F.dim α), ∑ j : Fin (F.dim α),
          ((F.rep α σ i j : ℝ) : ℂ) • vOp B π b a α i j) := by sorry

end PTCommutant.OperatorBasis
