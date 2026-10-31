-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_entropy_central_limit
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.entropy_central_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:06:31.765971+00:00
-- url     : https://prove2.me/theorems/c3041306-1b6e-4823-b51b-0926a2d0f166
-- title:
--   Corollary 3.3 — central limit theorem, with continuity-set correction
-- statement:
--   Assume detailed balance and positivity improvement at every positive time on $B(\mathbb C^d)$, $d>0$. Let $D_{jk}=\partial_k\partial_j e(0)$, and let $\mu_D$ be the centered Gaussian with covariance $D$, allowing singular $D$. For every initial density $\rho$ and Borel set $G$ with $\mu_D(\partial G)=0$,
--
--   $$\lim_{t\to\infty}P^t_\rho\{s:\sqrt t(s-\mathbb E_{\rho,t}s)\in G\}=\mu_D(G).$$
--
--   The covariance is positive semidefinite. Centering is by the actual finite-time mean. Gaussian continuity sets correct the printed unrestricted-Borel assertion and express the weak central limit theorem.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 9, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.9, Corollary 3.3. SOURCE CORRECTION: Gaussian continuity sets replace arbitrary
Borel sets. Singular covariance is allowed and centering uses the finite-time expectation. -/
theorem entropy_central_limit {d M : ℕ} (D : DBData d M) (hER : ER D) :
    ∀ rho, IsDensityMatrix rho → HasCLT (efcs D rho) (coordinateHessianAtZero (entropySpectralCGF D)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
