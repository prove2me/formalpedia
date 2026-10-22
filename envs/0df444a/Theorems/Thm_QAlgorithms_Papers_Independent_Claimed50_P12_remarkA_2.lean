-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_remarkA_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.remarkA_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:46:26.46019+00:00
-- url     : https://prove2.me/theorems/88cde522-5117-47b1-adc0-1806401bd671
-- title:
--   Scaling both one-shot entropies
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional system and let $\lambda>0$. For $0\le\epsilon\le\operatorname{tr}\rho$, the normalized testing entropy obeys
--
--   $$D_H^\epsilon(\rho\|\lambda\sigma)=D_H^\epsilon(\rho\|\sigma)-\log_2\lambda.$$
--
--   If $\rho$ is a density operator, the smooth max-relative entropy likewise satisfies $D_{\max}^\epsilon(\rho\|\lambda\sigma)=D_{\max}^\epsilon(\rho\|\sigma)-\log_2\lambda$ for every nonnegative smoothing parameter. The testing entropy at zero smoothing is the continuous right extension of the optimization value. Infinite values are retained. These identities fix the normalization used in Appendix A.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 19, Remark A.2

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

/-- Remark A.2, Eqs.144–145 (PDF p.19). Testing entropy includes epsilon=0
by its continuous extension; max entropy uses a density first argument. -/
theorem remarkA_2 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (lam : ℝ) (hlam : 0 < lam) :
    (∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ rho.trace.re →
      endpointTestingEntropyBits epsilon rho ((lam : ℂ) • sigma) =
        endpointTestingEntropyBits epsilon rho sigma - ((Real.logb 2 lam : ℝ) : EReal)) ∧
    (IsDensityMatrix rho → ∀ epsilon : ℝ, 0 ≤ epsilon →
      maxEntropy epsilon rho ((lam : ℂ) • sigma) =
        maxEntropy epsilon rho sigma - ((Real.logb 2 lam : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
