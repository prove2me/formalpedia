-- Prove2me | Theorems.Thm_PTCommutant_OperatorBasis_eq_86_E
-- name    : PTCommutant.OperatorBasis.eq_86_E
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:25.986272+00:00
-- url     : https://prove2.me/theorems/255c2a31-5b79-43aa-8da4-fbe775bc270f
-- title:
--   Eq. (86), first half, p. 17 — E^α_{ij} = (d_α/(n−2)!) Σ_{σ∈S(n−2)} φ^α_{ij}(σ) V(σ)
-- statement:
--   Let $\varphi^\alpha$ be real orthogonal, irreducible, pairwise inequivalent irreps of $S(n-2)$ of dimensions $d_\alpha$, and let $|\phi_i(\alpha,r)\rangle$ be an orthonormal basis of $(\mathbb C^d)^{\otimes(n-2)}$ with $V(\sigma)|\phi_j(\alpha,r)\rangle=\sum_i\varphi^\alpha_{ij}(\sigma)|\phi_i(\alpha,r)\rangle$. Let $E^\alpha_{ij}=\sum_r|\phi_i(\alpha,r)\rangle\langle\phi_j(\alpha,r)|$ (footnote 4). Then for every label $\alpha$ and all $i,j$:
--   $$E^\alpha_{ij}=\frac{d_\alpha}{(n-2)!}\sum_{\sigma\in S(n-2)}\varphi^\alpha_{ij}(\sigma)\,V(\sigma)\ \in\ \mathbb C[S(n-2)].$$
--
--   So the operators defined from the Schur basis are elements of the algebra of permutation operators; applying $\mathcal F^t_{ba}$ to this identity gives Theorem 9(a).
--
--   **Formalization Note.** $n=m+2$, $d_\alpha$ is `F.dim α`, $(n-2)!$ is `m.factorial`; the real matrix entries are cast to $\mathbb C$. $E^\alpha_{ij}$ is defined by footnote 4, not by the group sum, and the Schur basis carries no orthogonality relation, so the identity is not built into the definitions. If $\alpha$ has multiplicity $0$ in $(\mathbb C^d)^{\otimes(n-2)}$, both sides are $0$.
-- source:
--   Studziński, Horodecki, Mozrzymas, Commutant structuture of U⊗(n−1)⊗U* transformations, arXiv:1305.6183v2, p. 17, eq. (86) (first formula), recalled from eq. (24) p. 6; footnote 4 p. 6

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

namespace PTCommutant.OperatorBasis
open QAlgorithms.Schur

theorem eq_86_E {m d : ℕ} (F : IrrepFamily m) (B : SchurBasis F d) (α : F.ι)
    (i j : Fin (F.dim α)) :
    EOp B α i j =
      ((F.dim α : ℂ) / (m.factorial : ℂ)) •
        ∑ σ : Equiv.Perm (Fin m), ((F.rep α σ i j : ℝ) : ℂ) • tensorPermutation d m σ := by sorry

end PTCommutant.OperatorBasis
