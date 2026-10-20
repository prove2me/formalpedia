-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_proposition9
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.proposition9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:38:25.96927+00:00
-- url     : https://prove2.me/theorems/fac77997-0e72-4c99-97a3-4c9419ac1529
-- title:
--   Two-Bell-state mixture expansion
-- statement:
--   For $0<p<1$, put $v_\pm=(|01\rangle\pm|10\rangle)/\sqrt2$ and $\rho_p=p|v_+\rangle\langle v_+|+(1-p)|v_-\rangle\langle v_-|$. Fix $0<\varepsilon<1$ and $\Omega\in\{1\text{-LOCC},\mathrm{LOCC},\mathrm{SEP},\mathrm{PPT}\}$, with Alice-to-Bob one-way communication and completely PPT-preserving PPT maps. With $h_2(p)=-p\log_2p-(1-p)\log_2(1-p)$,
--
--   $$E_{D,\Omega}^{(1),\varepsilon}(\rho_p^{\otimes n})=n(1-h_2(p))+\sqrt{np(1-p)\left(\log_2\frac{1-p}{p}\right)^2}\,\Phi^{-1}(\varepsilon)+O(\log n).$$
--
--   The absolute remainder is bounded by $C\log_2n$ for every integer $n\ge N$, with some $C>0,N\ge2$ depending on $p,\varepsilon,\Omega$. Here $\Phi$ is the standard normal CDF, copies use the grouped Alice:Bob cut, and the one-shot quantity uses positive integer target rank and squared fidelity. The symmetric case $p=1/2$ is included. This gives explicit coefficients for phase-noise Bell mixtures.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 9, Proposition 9, Eqs. (48)–(49): two-Bell-state mixture

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Proposition 9, arXiv:1706.06221v3, PDF p.9, Eqs.(48)–(49).
The square on log stays inside the radical, including p>1/2 and p=1/2. -/
theorem proposition9 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (Omega : OperationClass) :
    secondOrderExpansion (fun n => oneShot Omega (copies (bellMixture p) n) epsilon)
      (1 - binEntropy2 p) (p * (1 - p) * (log2 ((1 - p) / p)) ^ 2) epsilon := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
