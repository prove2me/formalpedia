-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_iid_classicalSpectrum
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.iid_classicalSpectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:28:38.216289+00:00
-- url     : https://prove2.me/theorems/38f4ff22-d72c-442f-9d2d-382f666150d8
-- title:
--   Classical iid spectrum expansion including zero variance
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be normalized and $\sigma\ge0$ with support inclusion, and let $P,Q$ be their NS distributions. Write $D=D(\rho\Vert\sigma)$, let $V$ be the centered information variance, and fix $0<\varepsilon<1$. For $Z_i=\log P(X_i)-\log Q(X_i)$ under independent $P$ samples and every positive $n$,
--   $$D_s^\varepsilon(P^{\otimes n}\Vert Q^{\otimes n})=n\sup\{R:\Pr[n^{-1}\textstyle\sum_i Z_i\le R]\le\varepsilon\}.$$
--   If $V=0$, $D_s^a(P^{\otimes n}\Vert Q^{\otimes n})=nD$ for every positive $n$ and every $0\le a<1$, including zero. For every fixed real $c$,
--   $$D_s^{\varepsilon+c/\sqrt n}(P^{\otimes n}\Vert Q^{\otimes n})=nD+\sqrt{nV}\,\Phi^{-1}(\varepsilon)+O(1).$$
--   The last equality is two-sided with constants before $n$; its threshold ensures the shifted error lies in its true domain. This includes both signs in (33).
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 19, §VI Eqs. (31),(33): classical iid spectrum expansion

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

/-- Eqs.(31),(33), PDF pp.18--19: both signs of c/sqrt(n), and the explicit
V=0 identity for every error in [0,1), including zero. The zero shift is permitted. Constants may depend on c and epsilon. Source correction. Printed: Definition 1 p.7 prints V=Tr rho(log rho-log sigma)^2; p.19 prints Gaussian density exp(+x^2/2).
Changed: Use centered V=Tr rho(log rho-log sigma)^2-D^2 and the standard normal density exp(-x^2/2).
Why: Section VI identifies s^2 as Var(Z) and uses the standard normal Berry–Esseen theorem. For pure rho and sigma=I/d the likelihood is constant, hence V=0 even when D=log2(d) is nonzero. -/
theorem iid_classicalSpectrum (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (hsupport : SupportIncluded rho sigma)
    (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma)
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    (centeredRelativeVariance rho sigma = 0 → ∀ a : ℝ, 0 ≤ a → a < 1 → ∀ n : ℕ, 1 ≤ n →
      classicalSpectrumDivergence a (weightPower n (nsProbability r s)) (weightPower n (nsReferenceWeight r s)) =
        ((n * relativeMean rho sigma : ℝ) : EReal)) ∧
    (∀ n : ℕ, 1 ≤ n →
      classicalSpectrumDivergence e (weightPower n (nsProbability r s)) (weightPower n (nsReferenceWeight r s)) =
        (n : EReal) * sSup {v : EReal | ∃ R : ℝ,
          empiricalMeanMass n (nsProbability r s) (nsReferenceWeight r s) R ≤ e ∧ v = (R : EReal)}) ∧
    (∀ c : ℝ, ConstantRemainder
      (fun n => classicalSpectrumDivergence (e + c / Real.sqrt n)
        (weightPower n (nsProbability r s)) (weightPower n (nsReferenceWeight r s)))
      (fun n => gaussianCenter n (relativeMean rho sigma) (centeredRelativeVariance rho sigma) e)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
