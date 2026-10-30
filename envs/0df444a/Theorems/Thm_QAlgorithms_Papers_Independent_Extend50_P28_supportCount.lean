-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_supportCount
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.supportCount
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:19:37.396935+00:00
-- url     : https://prove2.me/theorems/b3f3dc93-57c9-4560-b1ed-777136cea661
-- title:
--   Exact support and count of the physical units
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Choose coherent lower-irrep coordinates. Embed the ordinary character projector $P_\mu$ on the first $n-1$ factors and the lower matrix unit $E^\alpha_{ij}$ on the first $n-2$ factors, each acting identically on the remaining factors. For physical shapes define $E^{\mu\nu}_{ij}(\alpha)=m_\alpha (m_\mu m_\nu)^{-1/2}P_\mu E^\alpha_{ij}T_NP_\nu$. A retained branch is a one-box extension of $\alpha$ having at most $d$ rows. Fix a physical lower shape $\alpha$, and allow $\mu,\nu$ to range over all physical size n-1 shapes. Let $b_\alpha$ count retained branches above $\alpha$. Then
--
--   $$
--   E^{\mu\nu}_{ij}(\alpha)\ne0\iff\mu/\alpha\text{ and }\nu/\alpha\text{ are single boxes},\qquad \#\{\text{distinct nonzero }E^{\mu\nu}_{ij}(\alpha)\}=(d_\alpha b_\alpha)^2.
--   $$
--
--   The count is the cardinality of an image of the physical operators after deleting zero, so it counts distinct matrices, not only index tuples.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 18, Remark 41

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.18, Remark 41, Eq.(87): exact support criterion over physical
shapes and the count of distinct nonzero physical matrices, rather than just
nonzero index tuples. Cardinal N is the number of retained branches. -/
theorem supportCount {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (hd : 2 ≤ d)
    (alpha : PhysicalLower d k) :
    (∀ (mu nu : PhysicalUpper d k) (i j : Fin (irrepDim alpha.val)),
      constructedE R d alpha.val mu nu i j ≠ 0 ↔
        oneBoxBranch alpha.val mu.val ∧ oneBoxBranch alpha.val nu.val) ∧
    (((Finset.univ : Finset ((PhysicalUpper d k × Fin (irrepDim alpha.val)) ×
        (PhysicalUpper d k × Fin (irrepDim alpha.val)))).image
        (fun pq => constructedE R d alpha.val pq.1.1 pq.2.1 pq.1.2 pq.2.2)).erase 0).card =
      (irrepDim alpha.val * Fintype.card (Retained d alpha.val)) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
