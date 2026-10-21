-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_formation_function_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P45.formation_function_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:51:21.026063+00:00
-- url     : https://prove2.me/theorems/4ffe7096-fe64-4c4c-a63f-8962a5a0faea
-- title:
--   Convexity and monotonicity of the formation function
-- statement:
--   For $0<t\le1$, define $c_\pm(t)=(t^{-1/2}\pm t^{1/2})^2/4$ and $f(t)=c_+(t)\log_2c_+(t)-c_-(t)\log_2c_-(t)$, with $0\log_2 0=0$. On this interval $f$ is convex and nonincreasing. For the normalized squeezed state and $r_t=-\tfrac12\ln t$,
--
--   $$E\bigl(\Psi_s(r_t)\bigr)=f(t),\qquad 0<t\le1.$$
--
--   Here $E$ is the actual extended spectral entropy of the first-mode reduction, in bits. In particular the endpoint $t=1$ is vacuum and $f(1)=0$. These properties provide the convexity and monotonicity ingredients for the symmetric Gaussian formation formula; no claim outside the stated interval is made.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 4, Unnumbered convexity, monotonicity and squeezed-entropy identity for f, Eqs.(17)-(18)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF pp.3–4, (17)–(18): convexity and decreasingness only on the specified
interval; identity with actual spectral entropy, including the vacuum endpoint. -/
theorem formation_function_properties :
    ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) gaussianFormationBits ∧
    AntitoneOn gaussianFormationBits (Set.Ioc (0 : ℝ) 1) ∧
    (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      pureEntanglement (squeezedVector (squeezingAt delta)) =
        ENNReal.ofReal (gaussianFormationBits delta)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
