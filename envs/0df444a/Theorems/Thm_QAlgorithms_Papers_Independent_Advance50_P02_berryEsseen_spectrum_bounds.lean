-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_berryEsseen_spectrum_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.berryEsseen_spectrum_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:29:42.282929+00:00
-- url     : https://prove2.me/theorems/07201628-07d6-4fa3-888b-9720d6845d7f
-- title:
--   Finite-n Berry–Esseen spectrum bounds
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. There exists a universal $0<C<1/2$ as follows. Let $\rho$ be normalized, $\sigma\ge0$ with support inclusion, $P,Q$ their NS pair, $D$ its mean, $V=s^2>0$ its centered variance, and $u=\mathbb E_P|\log P-\log Q-D|^3$. For $0<\varepsilon<1$, positive $n$, and $b_n=Cu/(s^3\sqrt n)<\min\{\varepsilon,1-\varepsilon\}$,
--   $$nD+\sqrt{nV}\,\Phi^{-1}(\varepsilon-b_n)\le D_s^\varepsilon(P^{\otimes n}\Vert Q^{\otimes n})\le nD+\sqrt{nV}\,\Phi^{-1}(\varepsilon+b_n).$$
--   The quantile and division domains are explicit. The printed undefined $r$ is interpreted as the preceding $t$, with $u=t^3$.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 19, §VI Eq. (32): finite-n spectrum bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Eq.(32), PDF p.19: universal Berry--Esseen C<1/2; the printed undefined r
is t, whose cube is the independently defined third absolute central moment. Source correction. Printed: Definition 1 p.7 omits centering; p.19 prints exp(+x^2/2) and undefined r^3 after defining t.
Changed: Use centered V, standard normal exp(-x^2/2), and t^3 equal to the third absolute central moment.
Why: Section VI explicitly uses Var(Z), the standard normal CDF, and numerator Ct^3 in its preceding Berry–Esseen bound. No separate r is defined. -/
theorem berryEsseen_spectrum_bounds :
    ∃ C : ℝ, 0 < C ∧ C < 1/2 ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (rho sigma : Mat I),
    QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef → SupportIncluded rho sigma →
    ∀ (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma) (e : ℝ), 0 < e → e < 1 →
    0 < centeredRelativeVariance rho sigma → ∀ n : ℕ, 1 ≤ n →
    let b := C * classicalThirdCentralMoment (nsProbability r s) (nsReferenceWeight r s) /
      ((Real.sqrt (centeredRelativeVariance rho sigma))^3 * Real.sqrt n)
    b < min e (1-e) →
    ((gaussianCenter n (relativeMean rho sigma) (centeredRelativeVariance rho sigma) (e-b) : ℝ) : EReal) ≤
      classicalSpectrumDivergence e (weightPower n (nsProbability r s)) (weightPower n (nsReferenceWeight r s)) ∧
    classicalSpectrumDivergence e (weightPower n (nsProbability r s)) (weightPower n (nsReferenceWeight r s)) ≤
      ((gaussianCenter n (relativeMean rho sigma) (centeredRelativeVariance rho sigma) (e+b) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
