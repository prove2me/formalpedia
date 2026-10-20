-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P19_ordinarySchur_subspaceRestriction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P19.ordinarySchur_subspaceRestriction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:13:24.969603+00:00
-- url     : https://prove2.me/theorems/6ca55e96-862b-44da-a0b2-bddf47d7d8ac
-- title:
--   Ordinary Schur sectors of a tensor-power subspace
-- statement:
--   Let $d,m\ge1$, let $S\subseteq\mathbb C^d$ be a complex linear subspace, and put $r=\dim S$ and $K=S^{\otimes m}$. Under the Schur decomposition into permutation and unitary irreducible factors,
--
--   $$U_{\mathrm{Sch}}^m(K)\subseteq\bigoplus_{\lambda\vdash_d m:\,\ell(\lambda)\le r} P_\lambda\otimes Q_\lambda^d.$$
--
--   Equivalently, for every vector $\psi\in K$ and every partition $\lambda$ of $m$ with at most $d$ rows and $\ell(\lambda)>r$, the full $\lambda$-isotypic projector satisfies $\Pi_\lambda\psi=0$. The statement includes $S=\{0\}$; it concerns the entire tensor-power subspace, including linear combinations of pure tensors.
--
--   This is the ordinary rank-subspace support restriction used before passing to mixed Schur sectors.
--
--   **Formalization Note** Lean uses the equivalent forbidden-projector formulation, with the accepted central character projector on computational tensor coordinates. Its range includes all permutation multiplicities. The subspace $K$ is constructed as the span of pure tensors with each factor in $S$.
-- source:
--   A memory and gate efficient algorithm for unitary mixed Schur sampling, arXiv:2410.15793v2, PDF p. 34, Eq. (C15)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Eq.(C15), ordinary subspace Schur restriction (arXiv:2410.15793v2,
PDF p.34). Stated in the equivalent basis-independent sector form: every
forbidden isotypic projector annihilates every vector of S tensor-power m.
The projector is the accepted central character projector, including all
Specht multiplicities. No rank assumption on an input density matrix is used. -/
theorem ordinarySchur_subspaceRestriction
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin d))) :
    ∀ psi ∈ tensorPowerSubspace m S,
      ∀ lambda : QAlgorithms.Schur.Partition d m,
        Module.finrank ℂ S < lambda.val.colLen 0 →
        QAlgorithms.act (QAlgorithms.Schur.isotypicProjector lambda) psi = 0 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P19

end
