-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_finiteBlock_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.finiteBlock_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:25:49.174537+00:00
-- url     : https://prove2.me/theorems/0de68f04-96f1-41f0-8fc3-7650d63afcc1
-- title:
--   Explicit finite-block compression and extraction bounds
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. There is a universal Berry–Esseen constant $0<C<1/2$ with the following property. Let $\rho_{XB}$ be a normalized finite CQ source and $0<\varepsilon<1$. Define $H=-D(\rho_{XB}\Vert I_X\otimes\rho_B)$, $s=\sqrt V>0$, and $u=\mathbb E_P|\log P-\log Q-D|^3=t^3$ from the pair's NS distributions. Restrict $\rho_B$ to its positive support to define $\lambda=\log\lambda_{\max}-\log\lambda_{\min}$, and put $k_n=\max\{1,\lceil n\lambda\rceil\}$ and $b_n=Cu/(\sqrt n\,s^3)$. For $0<\xi_0<\min\{\varepsilon,1-\varepsilon\}$ and $n>C^2u^2/(\xi_0^2s^6)$,
--   $$\begin{aligned}
--   \sup_{\xi_0\le\xi<1-\varepsilon}\left[-\sqrt n\,s\Phi^{-1}(\varepsilon+\xi)-\log\frac{2^9k_n}{(\xi-b_n)^4(1-\varepsilon-\xi)}\right]
--   &\le m^\varepsilon-nH\\
--   &\le\inf_{\xi_0\le\xi<\varepsilon}\left[-\sqrt n\,s\Phi^{-1}(\varepsilon-\xi)+\log\frac{2^2 3^3 k_n}{(\xi-b_n)^3}\right].
--   \end{aligned}$$
--   For $0<\xi_1<\min\{\varepsilon^2,1-\varepsilon^2\}$ and $n>C^2u^2/(\xi_1^2s^6)$,
--   $$\begin{aligned}
--   \sup_{\xi_1\le\xi<\varepsilon^2}\left[\sqrt n\,s\Phi^{-1}(\varepsilon^2-\xi)-\log\frac{5^5k_n}{(\xi-b_n)^5(1-\varepsilon)}\right]
--   &\le\ell^\varepsilon-nH\\
--   &\le\inf_{\xi_1\le\xi<1-\varepsilon^2}\left[\sqrt n\,s\Phi^{-1}(\varepsilon^2+\xi)+\log\frac{2^8 3^6 k_n}{(\xi-b_n)^6}\right].
--   \end{aligned}$$
--   Both operational quantities use $n$ iid copies. The positive-bin repair preserves flat marginals; the threshold makes every denominator positive. These are optimized finite-block bounds, not only asymptotic statements.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 21, Theorem 17: explicit finite-block bounds

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

/-- Theorem 17, PDF p.21: all four optimized finite-block bounds. The printed r
means t; its cube is classicalThirdCentralMoment. Positive variance is the division domain here,
not an extra assumption on the asymptotic corollaries. The flat-spectrum bin count
is corrected as required by the positive-bin proof on p.18. Source correction. Printed: Theorem 17 p.21 uses V from Definition 1, undefined r^3/r^6, and ceil(n lambda), with lambda using the minimum eigenvalue.
Changed: Use centered V and the standard normal CDF; interpret r=t; use max(1,ceil(n lambda)), evaluating lambda on the positive support of the actual marginal. V>0 is the division domain.
Why: Section VI identifies V as Var(Z) and defines t as the third-moment root. p.18 requires positive bins. A CQ state is supported on X tensor supp(rho_B), so restriction removes only unused kernel directions. All four constants, powers, intervals and blocklength thresholds remain. -/
theorem finiteBlock_bounds :
    ∃ C : ℝ, 0 < C ∧ C < 1/2 ∧
    ∀ (X B : Type) [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]
      (blocks : X → Mat B), NormalizedBlocks blocks →
    ∀ (r : PositiveSpectralPresentation (cqBlockMatrix blocks))
      (q : PositiveSpectralPresentation (identityTensor X (cqMarginal blocks)))
      (e : ℝ), 0 < e → e < 1 → 0 < cqConditionalVariance blocks →
    let s := Real.sqrt (cqConditionalVariance blocks)
    let u := classicalThirdCentralMoment (nsProbability r q) (nsReferenceWeight r q)
    (∀ xi0 : ℝ, 0 < xi0 → xi0 < min e (1-e) → ∀ n : ℕ,
      C^2 * u^2 / (xi0^2 * s^6) < (n : ℝ) →
      let b := C*u / (Real.sqrt n*s^3)
      let k : ℝ := finiteBins n (cqMarginal blocks)
      intervalSup xi0 (1-e) (fun xi => -Real.sqrt n*s*normalQuantile (e+xi) -
        logTwo ((2:ℝ)^9*k / ((xi-b)^4*(1-e-xi)))) ≤
          ((compressionLength e (blocksPower n blocks) : EReal) - (n*conditionalMean blocks : ℝ)) ∧
      ((compressionLength e (blocksPower n blocks) : EReal) - (n*conditionalMean blocks : ℝ)) ≤
        intervalInf xi0 e (fun xi => -Real.sqrt n*s*normalQuantile (e-xi) +
          logTwo ((2:ℝ)^2*3^3*k / (xi-b)^3))) ∧
    (∀ xi1 : ℝ, 0 < xi1 → xi1 < min (e^2) (1-e^2) → ∀ n : ℕ,
      C^2 * u^2 / (xi1^2 * s^6) < (n : ℝ) →
      let b := C*u / (Real.sqrt n*s^3)
      let k : ℝ := finiteBins n (cqMarginal blocks)
      intervalSup xi1 (e^2) (fun xi => Real.sqrt n*s*normalQuantile (e^2-xi) -
        logTwo ((5:ℝ)^5*k / ((xi-b)^5*(1-e)))) ≤
          ((extractionLength e (blocksPower n blocks) : EReal) - (n*conditionalMean blocks : ℝ)) ∧
      ((extractionLength e (blocksPower n blocks) : EReal) - (n*conditionalMean blocks : ℝ)) ≤
        intervalInf xi1 (1-e^2) (fun xi => Real.sqrt n*s*normalQuantile (e^2+xi) +
          logTwo ((2:ℝ)^8*3^6*k / (xi-b)^6))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
