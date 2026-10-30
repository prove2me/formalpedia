-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary43
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary43
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:14:40.553923+00:00
-- url     : https://prove2.me/theorems/4f78caf0-120d-49f3-818e-65602cf54c61
-- title:
--   Aggregated physical units: factorization and multiplication
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Choose coherent lower-irrep coordinates. Embed the ordinary character projector $P_\mu$ on the first $n-1$ factors and the lower matrix unit $E^\alpha_{ij}$ on the first $n-2$ factors, each acting identically on the remaining factors. For physical shapes define $E^{\mu\nu}_{ij}(\alpha)=m_\alpha (m_\mu m_\nu)^{-1/2}P_\mu E^\alpha_{ij}T_NP_\nu$. A retained branch is a one-box extension of $\alpha$ having at most $d$ rows. Put $P^{\mu\nu}(\alpha)=\sum_iE^{\mu\nu}_{ii}(\alpha)$ and let $P_\alpha$ be the embedded ordinary lower central character projector. All pairs in the product are retained branches of their respective physical lower shapes. Then
--
--   $$
--   P^{\mu\nu}(\alpha)=\frac{m_\alpha}{\sqrt{m_\mu m_\nu}}P_\mu P_\alpha T_NP_\nu,\qquad P^{\mu\nu}(\alpha)P^{\xi\omega}(\beta)=\delta_{\nu\xi}\delta_{\alpha\beta}P^{\mu\omega}(\alpha).
--   $$
--
--   Both concrete constructions (96) and the multiplication law (97) are retained. The last alpha can equally be beta on the nonzero branch.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 19, Corollary 43

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.19, Corollary 43, Eqs.(96)–(97): both concrete constructions and
multiplication of the aggregated units. Alpha is used on the nonzero RHS,
interchangeable with beta because equality is tested in that branch. -/
theorem corollary43 {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (hd : 2 ≤ d)
    (alpha beta : PhysicalLower d k) (mu nu xi omega : PhysicalUpper d k)
    (ham : oneBoxBranch alpha.val mu.val) (han : oneBoxBranch alpha.val nu.val)
    (hbx : oneBoxBranch beta.val xi.val) (hbo : oneBoxBranch beta.val omega.val) :
    aggregatedP R d alpha.val mu nu =
      ((tensorMultiplicity d alpha.val : ℂ) /
        (Real.sqrt ((tensorMultiplicity d mu.val : ℝ) * (tensorMultiplicity d nu.val : ℝ)) : ℂ)) •
      (embeddedProjector d mu.val extendPerm *
        embeddedProjector d alpha.val (fun sigma => extendPerm (extendPerm sigma)) *
        transposedSwap d (k + 1) (Fin.last k) * embeddedProjector d nu.val extendPerm) ∧
    aggregatedP R d alpha.val mu nu * aggregatedP R d beta.val xi omega =
      if nu = xi ∧ alpha = beta then aggregatedP R d alpha.val mu omega else 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
