-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaA_5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaA_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:42:11.126451+00:00
-- url     : https://prove2.me/theorems/d5760d89-3b32-4a27-a7a4-dc7b85cce721
-- title:
--   Hypothesis-testing entropy from a nearby dominated operator
-- statement:
--   Let $\rho,\bar\rho,\sigma\ge0$ on a nonzero finite-dimensional complex Hilbert space, and suppose $\bar\rho\le\lambda\sigma$ for $\lambda>0$. Let $\Delta$ be the generalized trace distance and assume $0<\epsilon\le\operatorname{tr}\rho$ and $\Delta(\rho,\bar\rho)<\epsilon$. Define $D_H^\epsilon=-\log_2\inf\{\operatorname{tr}(Q\sigma)/\epsilon:0\le Q\le1,\operatorname{tr}(Q\rho)\ge\epsilon\}$, with $-\log_2 0=+\infty$. Then
--
--   $$D_H^\epsilon(\rho\|\sigma)\le\log_2\lambda-\log_2\left(1-\frac{\Delta(\rho,\bar\rho)}\epsilon\right).$$
--
--   The positive logarithm argument makes explicit the domain used by the source proof; no finite logarithmic bound is assigned outside it. This estimate compares testing entropy with approximate operator domination.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 20, Lemma A.5

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

/-- Lemma A.5, Eq.149 (PDF p.20). The implicit logarithm domain is explicit:
Delta < epsilon <= tr rho, as required by Definition A.1 and the proof. -/
theorem lemmaA_5 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho bar sigma : Op I) (hrho : rho.PosSemidef) (hbar : bar.PosSemidef)
    (hsigma : sigma.PosSemidef) (lam epsilon : ℝ) (hlam : 0 < lam)
    (hbound : OperatorLE bar ((lam : ℂ) • sigma)) (hepsilon : 0 < epsilon)
    (htrace : epsilon ≤ rho.trace.re) (hdistance : generalizedTraceDistance rho bar < epsilon) :
    normalizedTestingEntropyBits epsilon rho sigma ≤
      ((Real.logb 2 lam - Real.logb 2 (1-generalizedTraceDistance rho bar/epsilon) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
