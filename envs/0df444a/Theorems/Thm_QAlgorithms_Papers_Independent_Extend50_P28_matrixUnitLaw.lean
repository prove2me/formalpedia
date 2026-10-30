-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_matrixUnitLaw
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.matrixUnitLaw
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:18:56.787322+00:00
-- url     : https://prove2.me/theorems/36164e16-5bd0-4e65-8e4b-d4148d63f12c
-- title:
--   Complete physical matrix-unit law and corner algebra
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Choose coherent lower-irrep coordinates. Embed the ordinary character projector $P_\mu$ on the first $n-1$ factors and the lower matrix unit $E^\alpha_{ij}$ on the first $n-2$ factors, each acting identically on the remaining factors. For physical shapes define $E^{\mu\nu}_{ij}(\alpha)=m_\alpha (m_\mu m_\nu)^{-1/2}P_\mu E^\alpha_{ij}T_NP_\nu$. A retained branch is a one-box extension of $\alpha$ having at most $d$ rows. Let $\mu,\nu$ be retained above $\alpha$ and $\xi,\omega$ retained above $\beta$. For valid internal indices,
--
--   $$
--   E^{\mu\nu}_{ij}(\alpha)E^{\xi\omega}_{rs}(\beta)=\delta_{\alpha\beta}\delta_{\nu\xi}\delta_{jr}E^{\mu\omega}_{is}(\alpha),\qquad \operatorname{span}_{\mathbb C}\{E^{\mu\nu}_{ij}(\alpha)\}\cong M_{d_\alpha b_\alpha}(\mathbb C),
--   $$
--
--   Here b_alpha is the number of retained branches of alpha. The explicit linear synthesis is a multiplicative bijection onto this physical span. Dependent indices are transported only when alpha=beta; the theorem does not claim the corner exhausts the whole mixed ideal.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 18, Section 4.2 unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF pp.18–19, Eq.(88) and the following isomorphism paragraph: all
cross-alpha matrix-unit products and the complete fixed-alpha corner algebra.
No claim is made that this corner exhausts the mixed ideal. -/
theorem matrixUnitLaw {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (hd : 2 ≤ d) :
    (∀ (alpha beta : PhysicalLower d k) (mu nu xi omega : PhysicalUpper d k),
      oneBoxBranch alpha.val mu.val → oneBoxBranch alpha.val nu.val →
      oneBoxBranch beta.val xi.val → oneBoxBranch beta.val omega.val →
      ∀ (i j : Fin (irrepDim alpha.val)) (r s : Fin (irrepDim beta.val)),
        constructedE R d alpha.val mu nu i j * constructedE R d beta.val xi omega r s =
          if h : alpha = beta then
            if nu = xi ∧ j.val = r.val then
              constructedE R d alpha.val mu omega i
                (Fin.cast (congrArg (fun a : PhysicalLower d k => irrepDim a.val) h.symm) s)
            else 0
          else 0) ∧
    (∀ alpha : PhysicalLower d k,
      IsMatrixAlgebraModel (fun p q : Retained d alpha.val × Fin (irrepDim alpha.val) =>
        constructedE R d alpha.val p.1.val q.1.val p.2 q.2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
