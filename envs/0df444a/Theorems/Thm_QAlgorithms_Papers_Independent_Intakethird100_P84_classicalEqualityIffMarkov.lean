-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_classicalEqualityIffMarkov
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.classicalEqualityIffMarkov
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:12:34.957481+00:00
-- url     : https://prove2.me/theorems/d9b8ba8d-382c-421c-be10-8f1237838e3b
-- title:
--   Section 5: classical equality iff Markov property (24)–(26)
-- statement:
--   Let $p(i,j,k)>0$ be a normalized finite joint probability law, retaining the invertibility domain of the classical discussion after Theorem 3. Compute its marginals $p_{12},p_{23},p_2$. Then
--
--   $$H(p)+H(p_2)=H(p_{12})+H(p_{23})\iff
--   \frac{p(i,j,k)}{p_{12}(i,j)}=\frac{p_{23}(j,k)}{p_2(j)}\quad\text{for all }i,j,k.$$
--
--   The displayed conditional-law identity is exactly (25). Both denominators are positive. Entropy uses the diagonal density and actual partial traces; its bit units preserve the equality.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 11, Section 5: classical equality iff Markov property (24)–(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.11, (24)--(26) [2,14].
The classical interpretation of Theorem 3 retains a strictly positive joint law.
All marginals and conditional denominators are computed from that law.
Entropy equality in bits is exactly the source equality in natural units. -/
theorem classicalEqualityIffMarkov {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (p : I × (J × K) → ℝ) (hpos : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1) :
    let rho : Matrix (I × (J × K)) (I × (J × K)) ℂ :=
      Matrix.diagonal (fun a => (p a : ℂ))
    (vnEntropy rho + vnEntropy (traceRight (traceLeft rho)) =
      vnEntropy (marginalAB rho) + vnEntropy (traceLeft rho)) ↔
    ∀ i j k, p (i, (j, k)) / (∑ l : K, p (i, (j, l))) =
      (∑ a : I, p (a, (j, k))) / (∑ a : I, ∑ l : K, p (a, (j, l))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
