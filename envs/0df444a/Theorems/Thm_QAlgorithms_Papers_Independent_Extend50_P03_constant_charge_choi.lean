-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_constant_charge_choi
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.constant_charge_choi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:03:47.790954+00:00
-- url     : https://prove2.me/theorems/cf469297-cfb3-40ef-bf09-75f6ffc90df4
-- title:
--   Appendix B: constant-charge average-state purified-distance scaling
-- statement:
--   Fix a nonnegative integer $\alpha$. In each of the two cases $k=t=1$ and $k=t=2$, let $\rho_{RE}=\operatorname{Tr}_{n-t}\Phi_{\rm avg}$ be the exact averaged normalized-EPR output of the charge-$\alpha$ code and let $\zeta_0=\operatorname{Tr}_R\rho_{RE}$. Then there are $C>0$ and $N$, depending on the fixed parameters, such that for every $n\ge N$ admitting the code,
--
--   $$P(\rho_{RE},I_R/2^k\otimes\zeta_0)\le Cn^{-1/2}.$$
--
--   This is the specific average-state term, not a lower or Theta bound on optimized channel error. The printed extra '+1' in the $k=t=2$ fidelity display is not used.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 23, Appendix B: constant-charge average-state purified-distance scaling

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix B, PDF p.23: the unambiguous closing scaling statement for k=t=1
and k=t=2, with alpha fixed. The printed extra '+1' in the k=t=2 fidelity
line is not promoted to a theorem. -/
theorem constant_charge_choi (alpha : ℕ) :
    ∀ k ∈ ({1,2} : Finset ℕ), ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, alpha+k ≤ n → k ≤ n →
      purified (reducedAverage n k alpha k) (comparisonChoi n k alpha k) ≤ C / Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
