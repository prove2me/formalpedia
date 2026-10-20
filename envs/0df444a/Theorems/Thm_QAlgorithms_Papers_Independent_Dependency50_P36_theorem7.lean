-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_theorem7
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.theorem7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:36:39.468792+00:00
-- url     : https://prove2.me/theorems/7b36ecd8-e5d4-4005-a8f7-8757deec8962
-- title:
--   General second-order distillation bounds
-- statement:
--   Fix a density operator $\rho$ on nonzero finite-dimensional $A\otimes B$, $0<\varepsilon<1$, an operation class $\Omega\in\{1\text{-LOCC},\mathrm{LOCC},\mathrm{SEP},\mathrm{PPT}\}$, and any Rains minimizer $\sigma\in\mathrm{PPT}'$. One-way communication is from Alice to Bob; PPT is completely PPT-preserving. Put $I=S(\rho_B)-S(\rho)$, $V_c=V(\rho\|I_A\otimes\rho_B)$, $V_s=V(\rho\|\sigma)$, where $S$ and $D$ use base-two logarithms and $V(\rho\|\tau)=\operatorname{Tr}\rho(\log_2\rho-\log_2\tau)^2-D(\rho\|\tau)^2$. The minimizer has support containing that of $\rho$. There exist finite $C>0$ and $N\ge2$ such that for every integer $n\ge N$,
--
--   $$nI+\sqrt{nV_c}\,\Phi^{-1}(\varepsilon)-C\log_2 n\ \le E_{D,\Omega}^{(1),\varepsilon}(\rho^{\otimes n})\ \le nR(\rho)+\sqrt{nV_s}\,\Phi^{-1}(\varepsilon)+C\log_2 n.$$
--
--   Here $\Phi$ is the standard normal CDF, copies are grouped as $A^n:B^n$, and one-shot entanglement uses integer target rank and squared target fidelity. Constants may depend on all fixed data, including the chosen minimizer. Zero variance is allowed. These explicit entropy and convex-optimization coefficients estimate total finite-blocklength entanglement; no uniform bit-complexity claim is made.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 7, Theorem 7, Eqs. (38)–(40): general second-order bounds

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

/-- Theorem 7, arXiv:1706.06221v3, PDF pp.7–8, Eqs.(38)–(40).
Use I=S(B)-S(AB)=+D(rho||I_A tensor rho_B), agreeing with the printed definition.
Constants are chosen after
rho, epsilon, the operation class and each Rains minimizer, but before copy number n. -/
theorem theorem7 {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) (Omega : OperationClass)
    (sigma : Matrix (A × B) (A × B) ℂ) (hsigma : pptPrime sigma)
    (hmin : relativeEntropy rho sigma = rains rho) :
    supportIncluded rho sigma ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
      (((n : ℝ) * stateCoherentInformationBits rho +
        Real.sqrt ((n : ℝ) * coherentVariance rho) * normalQuantile epsilon -
        C * log2 n : ℝ) : EReal) ≤ oneShot Omega (copies rho n) epsilon ∧
      oneShot Omega (copies rho n) epsilon ≤
        (((n : ℝ) * relativeEntropyFinite rho sigma +
          Real.sqrt ((n : ℝ) * pairInformationVariance rho sigma) * normalQuantile epsilon +
          C * log2 n : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
