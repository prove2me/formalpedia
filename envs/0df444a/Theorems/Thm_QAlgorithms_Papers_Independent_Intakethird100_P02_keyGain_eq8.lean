-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P02_keyGain_eq8
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P02.keyGain_eq8
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:47:15.926877+00:00
-- url     : https://prove2.me/theorems/16692680-1337-4251-aa0a-3aafddc19677
-- title:
--   Ideal-correction gain and its positive-tail representation
-- statement:
--   Let $n>0$, $0<\eta\le1$ and a finite real threshold $x_0\ge0$ specify the equiprobable four-state protocol with homodyne postselection and ideal error correction. Set $v=1/4$ and $a=\sqrt{\eta n}$. The unconditioned homodyne density in a matching basis is
--   $$
--   p(x)=\frac{e^{-(x-a)^2/(2v)}+e^{-(x+a)^2/(2v)}}{2\sqrt{2\pi v}}.
--   $$
--   Let $q(x)$ be the likelihood of the positive signal divided by the sum of both signal likelihoods, and put $i_{AB}(x)=1+q(x)\log_2q(x)+(1-q(x))\log_2(1-q(x))$. Define $G$ as one half of the integral of $p(x)(i_{AB}(x)-I^R_{\mathrm{opt}})$ over $|x|>x_0$, where the leakage is independently optimized over individual measurements. The full-line integrand is integrable, and
--   $$
--   \begin{aligned}
--   G(x_0,n,\eta)
--   &=\frac12\int_{|x|>x_0}p(x)\left[i_{AB}(x)-\log_2\!\left(2-e^{-(1-\eta)n/v}\right)\right]dx\\
--   &=\int_{x>x_0}p(x)\left[i_{AB}(x)-\log_2\!\left(2-e^{-(1-\eta)n/v}\right)\right]dx.
--   \end{aligned}
--   $$
--   The factor $1/2$ accounts for basis matching. The gain is per emitted pulse, is not conditioned on acceptance, and may be negative at an arbitrary threshold.
--
--   This is the paper's asymptotic ideal-correction gain against the stated individual splitting attack, rather than an unconditional security assertion.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, PDF p. 2, Eq.(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P02

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator coherentKet coherentCoefficient)

open QAlgorithms.Papers.Independent.Frontier30.P21 (coherentDensity)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal quadrature)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity productCoeff)

/-- PDF p.2, (8): the density-weighted continuous interpretation of the printed
sums, including the closed leakage expression and the positive-tail identity. -/
theorem keyGain_eq8 (x0 n eta : ℝ) (hx0 : 0 ≤ x0) (hn : 0 < n)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) :
    Integrable (fun x => binaryDensity (1 / 4 : ℝ) (eta * n) x *
      (homodyneInformation (1 / 4 : ℝ) (eta * n) x - optimalLeakage n eta)) ∧
    splittingGain x0 n eta =
      (1 / 2 : ℝ) * (∫ x in {x : ℝ | x0 < |x|},
        binaryDensity (1 / 4 : ℝ) (eta * n) x *
          (homodyneInformation (1 / 4 : ℝ) (eta * n) x -
            Real.logb 2 (2 - Real.exp (-((1 - eta) * n) / (1 / 4 : ℝ))))) ∧
    splittingGain x0 n eta =
      ∫ x in Set.Ioi x0, binaryDensity (1 / 4 : ℝ) (eta * n) x *
        (homodyneInformation (1 / 4 : ℝ) (eta * n) x -
          Real.logb 2 (2 - Real.exp (-((1 - eta) * n) / (1 / 4 : ℝ)))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P02

end
