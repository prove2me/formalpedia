-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_correlated_cutoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.correlated_cutoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:40:52.81999+00:00
-- url     : https://prove2.me/theorems/be35c528-20bb-4a52-9c60-9ef1809f5eb1
-- title:
--   Theorem III.4: correlated-state cutoff identities
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $H_n$ be arbitrary finite-dimensional spaces and $\rho_n,\sigma_n$ density operators. Let $c:\mathbb N\to\mathbb N$ be nondecreasing and tend to infinity. Assume $c(n)^{-1}(a-1)S_a(\rho_n\|\sigma_n)$ converges to a real function $\psi(a)$ uniformly for $0\le a<1$, and $\psi$ is differentiable on $(0,1)$. Write $\overline S_a$ for the mean divergence, obtained by dividing by $c(n)$ and taking the limit. Define $C_\kappa(\vec\rho\|\vec\sigma)$ operationally using actual effects, the scale $1/c(n)$, the strict first-kind limsup constraint, and the upper second-kind exponent, extended at $r=0$ by its right limit. Then
--
--   $$C_\kappa(\vec\rho\|\vec\sigma)=\frac1{|\kappa|}\overline S_{|\kappa|/(1+|\kappa|)}(\vec\rho\|\vec\sigma)=\overline S_{1/(1+|\kappa|)}(\vec\sigma\|\vec\rho)\quad(\kappa<0).$$
--
--   Equivalently, for $0<a<1$, $\overline S_a(\vec\rho\|\vec\sigma)=\frac a{1-a}C_{a/(a-1)}(\vec\rho\|\vec\sigma)=C_{(a-1)/a}(\vec\sigma\|\vec\rho)$. No reverse-sequence regularity assumption is imposed. This extends the cutoff identity beyond independent copies.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 5, Theorem III.4: correlated-state cutoff identities

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Theorem III.4, PDF pp.5–6: both parameterizations for correlated sequences.
Only the forward real limiting log trace has regularity hypotheses. -/
theorem correlated_cutoff {J : ℕ → Type} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (rho sigma : (n : ℕ) → Operator (J n))
    (hrho : ∀ n, IsDensityMatrix (rho n)) (hsigma : ∀ n, IsDensityMatrix (sigma n))
    (c : ℕ → ℕ) (hc : Monotone c) (hc_infty : Tendsto c atTop atTop)
    (psi : ℝ → ℝ) (huniform : UniformLogTraceLimit c rho sigma psi)
    (hdiff : DifferentiableOn ℝ psi (Ioo 0 1)) :
    (∀ k : ℝ, k < 0 → testingCutoff c rho sigma k =
      ((1 / |k| : ℝ) : EReal) * meanRenyi c rho sigma (|k| / (1 + |k|)) ∧
      ((1 / |k| : ℝ) : EReal) * meanRenyi c rho sigma (|k| / (1 + |k|)) =
        meanRenyi c sigma rho (1 / (1 + |k|))) ∧
    (∀ a : ℝ, 0 < a → a < 1 → meanRenyi c rho sigma a =
      ((a / (1 - a) : ℝ) : EReal) * testingCutoff c rho sigma (a / (a - 1)) ∧
      meanRenyi c rho sigma a = testingCutoff c sigma rho ((a - 1) / a)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
