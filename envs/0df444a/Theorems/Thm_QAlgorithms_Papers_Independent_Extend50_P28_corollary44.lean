-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary44
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary44
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:15:22.252108+00:00
-- url     : https://prove2.me/theorems/2f7aeb37-3493-46e3-96aa-5a58b8003800
-- title:
--   Fixed-branch physical matrix algebra
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Choose coherent lower-irrep coordinates. Embed the ordinary character projector $P_\mu$ on the first $n-1$ factors and the lower matrix unit $E^\alpha_{ij}$ on the first $n-2$ factors, each acting identically on the remaining factors. For physical shapes define $E^{\mu\nu}_{ij}(\alpha)=m_\alpha (m_\mu m_\nu)^{-1/2}P_\mu E^\alpha_{ij}T_NP_\nu$. A retained branch is a one-box extension of $\alpha$ having at most $d$ rows. Fix a physical lower shape $\alpha$ and retained branch $\nu$. Then
--
--   $$
--   E^{\nu\nu}_{ij}(\alpha)E^{\nu\nu}_{rs}(\alpha)=\delta_{jr}E^{\nu\nu}_{is}(\alpha),\qquad \operatorname{span}_{\mathbb C}\{E^{\nu\nu}_{ij}(\alpha)\}\cong M_{d_\alpha}(\mathbb C).
--   $$
--
--   The explicit synthesis map from coefficient matrices is complex linear, multiplicative and injective, with image exactly the physical span. Thus the algebra-isomorphism clause is fully retained.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 20, Corollary 44

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.20, Corollary 44, Eq.(98): full matrix-unit multiplication and
isomorphism of their physical span with M_(d_alpha)(C), both retained. -/
theorem corollary44 {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (hd : 2 ≤ d)
    (alpha : PhysicalLower d k) (nu : Retained d alpha.val) :
    (∀ i j r s : Fin (irrepDim alpha.val),
      constructedE R d alpha.val nu.val nu.val i j * constructedE R d alpha.val nu.val nu.val r s =
        if j = r then constructedE R d alpha.val nu.val nu.val i s else 0) ∧
    IsMatrixAlgebraModel (fun i j => constructedE R d alpha.val nu.val nu.val i j) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
