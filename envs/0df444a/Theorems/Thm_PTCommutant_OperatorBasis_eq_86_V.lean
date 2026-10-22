-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_eq_86_V
-- name    : PTCommutant.OperatorBasis.eq_86_V
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:30.883484+00:00
-- url     : https://prove2.me/theorems/b1d64e1a-fcef-4d0a-8712-83657a812a6f
-- title:
--   Eq. (86), second half, p. 17 — V(σ) = ⊕_α Σ_{ij} φ^α_{ij}(σ) E^α_{ij}
-- statement:
--   Under the same standing data as eq. (86), first half (real orthogonal, irreducible, pairwise inequivalent irreps $\varphi^\alpha$ of $S(n-2)$ and an adapted orthonormal Schur basis $|\phi_i(\alpha,r)\rangle$ of $(\mathbb C^d)^{\otimes(n-2)}$), with $E^\alpha_{ij}=\sum_r|\phi_i(\alpha,r)\rangle\langle\phi_j(\alpha,r)|$, every permutation operator of $S(n-2)$ decomposes as
--   $$V(\sigma)=\bigoplus_\alpha\sum_{i,j}\varphi^\alpha_{ij}(\sigma)\,E^\alpha_{ij},\qquad\sigma\in S(n-2).$$
--
--   Applying $\mathcal F^t_{ab}$ to this identity gives Theorem 9(b).
--
--   **Formalization Note.** $n=m+2$; the direct sum $\bigoplus_\alpha$ is a sum over all labels of the family, since the $E^\alpha_{ij}$ of different labels act on orthogonal subspaces.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 17, eq. (86) (second formula), recalled from eq. (24) p. 6

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem eq_86_V {m d : ℕ} (F : IrrepFamily m) (B : SchurBasis F d)
    (σ : Equiv.Perm (Fin m)) :
    tensorPermutation d m σ =
      ∑ α : F.ι, ∑ i : Fin (F.dim α), ∑ j : Fin (F.dim α),
        ((F.rep α σ i j : ℝ) : ℂ) • EOp B α i j := by sorry

end PTCommutant.OperatorBasis
