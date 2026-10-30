-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_corollary57
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.corollary57
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:17:53.681614+00:00
-- url     : https://prove2.me/theorems/44f4fd89-d229-45c1-812e-17d7f398c74e
-- title:
--   Physical dimension identity and its normalization
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Let $\dim\Phi^\alpha=\operatorname{rank}Q_\alpha$, the dimension of the independently computed Gram-range carrier. Let $M_\nu$ be the dimension of the intertwiner space from the Specht module $\nu$ into physical tensor space, intertwining the ordinary $S(n-1)$ subgroup and annihilated by every $T_a$; this counts actual second-kind copies. Then
--
--   $$
--   d^n=\sum_{h(\alpha)\le d}m_\alpha\dim\Phi^\alpha+\sum_{h(\nu)<d}M_\nu d_\nu,\qquad 1=\frac{\sum_{h(\alpha)\le d}m_\alpha\dim\Phi^\alpha}{d^n}+\frac{\sum_{h(\nu)<d}M_\nu d_\nu}{d^n}.
--   $$
--
--   The first sum ranges over size n-2 shapes, the second over size n-1 shapes. Both (130) and (131) are stated; no incorrect multiplicity subtraction is used.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 25, Corollary 57

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.25, Corollary 57, Eqs.(130)–(131), with n=k+2. Both the integer
dimension identity and its normalized form are retained. The first-kind carrier
has dimension rank Q by (16); M_nu is counted in physical tensor space independently. -/
theorem corollary57 {k : ℕ} (R : CoherentPRIR k) (d : ℕ) (hd : 2 ≤ d) :
    d ^ (k + 2) =
      (∑ alpha : PhysicalLower d k, tensorMultiplicity d alpha.val * firstKindDimension R alpha.val d) +
      (∑ nu : SecondShapes d (k + 1), secondKindMultiplicity d nu.val * irrepDim nu.val) ∧
    (1 : ℝ) =
      (∑ alpha : PhysicalLower d k,
        (tensorMultiplicity d alpha.val : ℝ) * (firstKindDimension R alpha.val d : ℝ)) /
        (d : ℝ) ^ (k + 2) +
      (∑ nu : SecondShapes d (k + 1),
        (secondKindMultiplicity d nu.val : ℝ) * (irrepDim nu.val : ℝ)) /
        (d : ℝ) ^ (k + 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
