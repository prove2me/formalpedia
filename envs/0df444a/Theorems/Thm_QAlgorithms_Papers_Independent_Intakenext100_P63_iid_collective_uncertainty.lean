-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P63_iid_collective_uncertainty
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P63.iid_collective_uncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:18:16.002983+00:00
-- url     : https://prove2.me/theorems/7ea3a11e-ab23-4cc2-abc0-d344ef767427
-- title:
--   IID ensemble uncertainty against collective measurements
-- statement:
--   Let $p=(p_i)_{i=1}^d$ be a probability vector with $d\ge1$, and let every $\rho_i$ be a normalized density on a nonzero finite-dimensional environment $E$. Set $\bar\rho=\sum_ip_i\rho_i$ and $M_i=\bar\rho^{-1/2}p_i\rho_i\bar\rho^{-1/2}$. View $M$ as a POVM on $\operatorname{supp}\bar\rho$ and let $\widehat H(M)$ be its minimum output Shannon entropy there. Let $I_1,\ldots,I_n$ be IID with law $p$; for any finite collective POVM $Q$ on $E^{\otimes n}$, define $\Pr(I^n=i^n,J=j)=\prod_tp_{i_t}\operatorname{Tr}[(\bigotimes_t\rho_{i_t})Q_j]$. For $0<\varepsilon,\delta<1$,
--
--   $$H_{\min}^{\varepsilon}(I^n|J)\ge n(\widehat H(M)-\delta)-\frac{16(\log_2d)^2}{\delta}\log_2\frac1\varepsilon.$$
--
--   For sufficiently large $n$, uniformly over $Q$,
--
--   $$H_{\min}^{\varepsilon}(I^n|J)\ge n\widehat H(M)-8\log_2d\sqrt{n\log_2(1/\varepsilon)}.$$
--
--   All entropies are in bits; smoothing is over normalized joint densities at half trace-norm distance. The preparation labels are independent; Eve's measurement need not be a product measurement. Zero prior weights and rank-deficient average states remain allowed.
-- source:
--   Weak locking capacity of quantum channels can be much larger than private capacity, arXiv:1403.6361v3, PDF p. 9, Corollary 9: IID ensemble uncertainty against collective measurements

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P63

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower dilationMap SupportIncluded)

open QAlgorithms.Papers.Independent.Bridge50.P47 (SymmetricIndex universalSymmetricDilation)

open QAlgorithms.Learning (IsDistribution)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Corollary 9: IID labels and arbitrary collective environment POVMs.
The associated minimum is on supp(rho-bar); d counts labels, not Eve's outcomes. -/
theorem iid_collective_uncertainty {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (d : ℕ) (hd : 0 < d) (p : Fin d → ℝ) (hp : IsDistribution p)
    (rho : Fin d → Mat E) (hrho : ∀ i, IsDensityMatrix (rho i))
    (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1) :
    (∀ delta : ℝ, 0 < delta → delta < 1 → ∀ n : ℕ,
      ∀ Q : Measurement (Fin n → E),
      (n : ℝ) * (associatedMinimum p rho - delta) -
        16 * (Real.logb 2 d) ^ 2 / delta * Real.logb 2 (1 / eps) ≤
        traceSmoothConditionalMinBits eps (classicalJoint (iidJoint p rho n Q))) ∧
    (∃ n0 : ℕ, ∀ n ≥ n0, ∀ Q : Measurement (Fin n → E),
      (n : ℝ) * associatedMinimum p rho -
        8 * Real.logb 2 d * Real.sqrt ((n : ℝ) * Real.logb 2 (1 / eps)) ≤
        traceSmoothConditionalMinBits eps (classicalJoint (iidJoint p rho n Q))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P63

end
