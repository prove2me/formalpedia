-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_upsilonMinMaxBound
-- name    : QAlgorithms.Papers.Independent.Support50.P23.upsilonMinMaxBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:09:00.34354+00:00
-- url     : https://prove2.me/theorems/098479cb-5130-4ba2-8caa-d58fbc58160b
-- title:
--   Min/max control of the convergence parameter
-- statement:
--   Let $\rho_{AB}$ be a normalized finite-dimensional state and $\rho_B=\operatorname{tr}_A\rho_{AB}$. With all entropies in bits, both
--   $$
--   H_{3/2}(A|B)_{\rho|\rho_B}\ge H_{\min}(A|B)_\rho
--   $$
--   and
--   $$
--   \Upsilon(A|B)_{\rho|\rho_B}\le
--   \sqrt{2^{-H_{\min}(A|B)_\rho}}+\sqrt{2^{H_{\max}(A|B)_\rho}}+1
--   $$
--   hold. Here $\Upsilon=2^{-H_{3/2}/2}+2^{H_{1/2}/2}+1$ uses the fixed reference $\rho_B$, whereas the min and max entropies on the right are optimized. This controls convergence without a dimension-of-$B$ factor.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 5, Section IV, unnumbered: min/max bound on convergence parameter

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

/-- Section IV, PDF p.5: both the H_{3/2} comparison and dimension-free min/max
bound on the COMPUTED convergence parameter. -/
theorem upsilonMinMaxBound [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    minEntropy rho ≤ finiteAlpha rho (traceLeft rho) (3 / 2) ∧
      entropyConvergenceParameter rho (traceLeft rho) ≤
        exp2Extended (-minEntropy rho * ((1 / 2 : ℝ) : EReal)) +
          exp2Extended (dualMaxEntropy rho * ((1 / 2 : ℝ) : EReal)) + 1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
