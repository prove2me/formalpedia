-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_two_term_positive_part
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.two_term_positive_part
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:21:49.690957+00:00
-- url     : https://prove2.me/theorems/dbb978cc-bebe-4658-85ee-21f62910aa5c
-- title:
--   Lemma III.6: two-term finite-copy positive-part bound
-- statement:
--   Let $\rho,\sigma$ be normalized density operators on a nonzero finite-dimensional Hilbert space $H$ with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Let $n\ge1$, $\lambda,\mu\in\mathbb R$, and $s\in[0,1]$. Inverses of $\sigma$ are taken on its support. Then
--   $$
--   \operatorname{Tr}(\rho^{\otimes n}-2^{\lambda n}\sigma^{\otimes n})_+
--   \le2^{-n(s\mu-\log_2\operatorname{Tr}\rho^{1+s})}
--   +2^{-n\left(s(\lambda-\mu)-s\dim(H)\frac{\log_2(1+n)}n-\log_2\operatorname{Tr}(\rho\sigma^{-s})\right)}.
--   $$
--
--   The two moments are distinct, and the polynomial correction belongs inside the second exponent. Full rank of sigma is not required.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 14, Lemma III.6: two-term finite-copy positive-part bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.14--16 Lemma III.6 Eq.(78), checked in rendered PDF p.14.
The second moment is Tr(rho sigma^(-s)), and the polynomial correction is
SUBTRACTED INSIDE the second exponent. No full-rank sigma assumption. -/
theorem two_term_positive_part {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin)
    (n : ℕ) (hn : 0 < n) (lambda mu s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (positivePart (piKron n rho - (((2 : ℝ) ^ (lambda * n) : ℝ) : ℂ) • piKron n sigma)).trace.re ≤
      (2 : ℝ) ^ (-(n : ℝ) * (s * mu -
        Real.logb 2 (cfc (fun x : ℝ => x ^ (1 + s)) rho).trace.re)) +
      (2 : ℝ) ^ (-(n : ℝ) * (s * (lambda - mu) -
        s * Fintype.card I * Real.logb 2 (1 + (n : ℝ)) / n -
        Real.logb 2 (rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (-s)) sigma).trace.re)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
