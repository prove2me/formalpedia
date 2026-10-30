-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_proposition42
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.proposition42
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:13:55.494203+00:00
-- url     : https://prove2.me/theorems/555182d3-d100-4255-ab09-22c98800f005
-- title:
--   Physical generator expansion in constructed matrix units
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Choose coherent lower-irrep coordinates. Embed the ordinary character projector $P_\mu$ on the first $n-1$ factors and the lower matrix unit $E^\alpha_{ij}$ on the first $n-2$ factors, each acting identically on the remaining factors. For physical shapes define $E^{\mu\nu}_{ij}(\alpha)=m_\alpha (m_\mu m_\nu)^{-1/2}P_\mu E^\alpha_{ij}T_NP_\nu$. A retained branch is a one-box extension of $\alpha$ having at most $d$ rows.
--
--   $$
--   T_N=\sum_{\substack{\alpha\vdash n-2\\h(\alpha)\le d}}\ \sum_{\mu,\nu\text{ retained above }\alpha}\ \sum_{i=1}^{d_\alpha}\frac{\sqrt{m_\mu m_\nu}}{m_\alpha}E^{\mu\nu}_{ii}(\alpha).
--   $$
--
--   This is equality of concrete operators on the entire tensor space; no irrep representation is supplied as a free parameter.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 19, Proposition 42

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.19, Proposition 42, Eq.(95): equality of physical tensor-space
operators, summed over every physical lower shape and retained pair. -/
theorem proposition42 {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (hd : 2 ≤ d) :
    transposedSwap d (k + 1) (Fin.last k) =
      ∑ alpha : PhysicalLower d k, ∑ mu : Retained d alpha.val, ∑ nu : Retained d alpha.val,
        ∑ i : Fin (irrepDim alpha.val),
          ((Real.sqrt ((tensorMultiplicity d mu.val.val : ℝ) *
            (tensorMultiplicity d nu.val.val : ℝ)) / (tensorMultiplicity d alpha.val : ℝ) : ℝ) : ℂ) •
            constructedE R d alpha.val mu.val nu.val i i := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
