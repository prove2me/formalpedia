-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_pureInputExtrema
-- name    : QAlgorithms.Papers.Independent.Support50.P31.pureInputExtrema
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:23:27.886659+00:00
-- url     : https://prove2.me/theorems/3f026a15-856c-4297-a3db-c544c622bde0
-- title:
--   Pure inputs attain all the output-purity extrema
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving linear endomorphism of the operators on a nonzero finite-dimensional complex Hilbert space. A density matrix is a positive semidefinite operator of trace one. Write $H(\rho)=-\operatorname{Tr}(\rho\log\rho)$ in natural units, with $0\log0=0$; write $\|\rho\|_p$ for the Schatten $p$-norm, allowing $p=\infty$ for the operator norm, and $\lambda_{\min}(\rho)$ for the least eigenvalue including zero. There exist unit vectors attaining each of the following extrema:
--   $$
--   \begin{aligned}
--   \max_\rho\|\Phi(\rho)\|_p
--    &=\|\Phi(|v_p\rangle\langle v_p|)\|_p &&(1\le p\le\infty),\\
--   \min_\rho H(\Phi(\rho))
--    &=H(\Phi(|v_H\rangle\langle v_H|)),\\
--   \min_\rho\lambda_{\min}(\Phi(\rho))
--    &=\lambda_{\min}(\Phi(|v_-\rangle\langle v_-|)).
--   \end{aligned}
--   $$
--   The extrema range over all density inputs. Different objectives may have different optimizing vectors. The assertion supplies pure optimizers and does not claim that every optimizer is pure.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 3, §2, pure-input attainment of output-purity extrema

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.3–4: existence of pure optimizers for (4)–(6), not exclusivity.
Includes p = 1, infinity, and zero least eigenvalues. -/
theorem pureInputExtrema {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (Phi : Superop I I) (hPhi : IsChannel Phi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧
      pPurity p (Phi (pureDensity v)) = nuP p Phi) ∧
    (∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ entropy (Phi (pureDensity v)) = nuH Phi) ∧
    (∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧
      minEigenvalue (Phi (pureDensity v)) = nuMinus Phi) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
