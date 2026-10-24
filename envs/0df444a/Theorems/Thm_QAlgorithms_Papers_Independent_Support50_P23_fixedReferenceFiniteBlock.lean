-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_fixedReferenceFiniteBlock
-- name    : QAlgorithms.Papers.Independent.Support50.P23.fixedReferenceFiniteBlock
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:03:07.25332+00:00
-- url     : https://prove2.me/theorems/d1c99b2c-a1a2-4e2c-a2cf-8b29e0d810cf
-- title:
--   Fixed-reference finite-block AEP
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states and let $n\ge1$. Define $\eta=\Upsilon(A|B)_{\rho|\sigma}$ and $\delta(\varepsilon,\eta)=4\log_2\eta\sqrt{\log_2(2/\varepsilon^2)}$. On the branch $\eta<\infty$, if $0<\varepsilon<1$ and $n\ge\frac85\log_2(2/\varepsilon^2)$, then
--   $$
--   \frac1n H_{\min}^{\varepsilon}(A^n|B^n)_{\rho^{\otimes n}|\sigma^{\otimes n}}
--   \ge H(A|B)_{\rho|\sigma}-\frac{\delta(\varepsilon,\eta)}{\sqrt n}.
--   $$
--   If the support of $\rho_{AB}$ is not contained in that of $I_A\otimes\sigma_B$, the fixed-reference von Neumann entropy is $-\infty$, yielding the trivial lower bound. For $\varepsilon\ge1$, the smooth fixed min entropy is $+\infty$. This version retains the exact reference tensor power.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 6, Remark 10: fixed-reference finite-block AEP

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Remark 10, PDF p.6: sigma^{tensor n} remains fixed. Use the finite-eta formula
only on its real domain; support failure is a -infinity lower bound. The epsilon
domain correction is the same as in Theorem 9. -/
theorem fixedReferenceFiniteBlock [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ entropyConvergenceParameter rho sigma ≠ ⊤ ∧
        (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      fixedVonNeumann rho sigma -
        ((aepBlockError epsilon (entropyConvergenceParameter rho sigma) / Real.sqrt (n : ℝ) : ℝ) : EReal) ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal) *
            sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon) ∧
    (¬ supportedBy rho (identityTensorReference (A := A) sigma) →
      fixedVonNeumann rho sigma = ⊥ ∧ fixedVonNeumann rho sigma ≤
        (((n : ℝ)⁻¹ : ℝ) : EReal) *
          sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon) ∧
    (1 ≤ epsilon → sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
