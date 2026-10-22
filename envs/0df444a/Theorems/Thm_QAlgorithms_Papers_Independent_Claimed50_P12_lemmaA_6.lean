-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaA_6
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaA_6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:43:16.057487+00:00
-- url     : https://prove2.me/theorems/15f0d022-f906-49de-98e4-cb7330bab84b
-- title:
--   Testing entropy bounded by smoothed max-relative entropy
-- statement:
--   Let $\rho$ be a density operator and $\sigma\ge0$ on a nonzero finite-dimensional complex Hilbert space. Let $0\le\epsilon'<\epsilon\le1$. Write $D_H^\epsilon$ for Definition A.1 testing entropy and $D_{\max}^{\epsilon'}$ for the infimum of $\log_2\lambda$ over $\lambda>0$ and $\bar\rho\ge0$ with $\operatorname{tr}\bar\rho\le1$, $1-F(\bar\rho,\rho)^2\le(\epsilon')^2$, and $\bar\rho\le\lambda\sigma$. Then, in the extended real order,
--
--   $$D_H^\epsilon(\rho\|\sigma)\le D_{\max}^{\epsilon'}(\rho\|\sigma)+\log_2\frac\epsilon{\epsilon-\epsilon'}.$$
--
--   The denominator is positive, $\epsilon'=0$ is allowed, and root fidelity is used. This connects the two one-shot relative entropies.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 20, Lemma A.6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma A.6, Eq.152 (PDF p.20): infinity retained, epsilonPrime=0 allowed. -/
theorem lemmaA_6 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (epsilon epsilonPrime : ℝ) (hzero : 0 ≤ epsilonPrime)
    (hlt : epsilonPrime < epsilon) (hone : epsilon ≤ 1) :
    normalizedTestingEntropyBits epsilon rho sigma ≤ maxEntropy epsilonPrime rho sigma +
      ((Real.logb 2 (epsilon/(epsilon-epsilonPrime)) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
