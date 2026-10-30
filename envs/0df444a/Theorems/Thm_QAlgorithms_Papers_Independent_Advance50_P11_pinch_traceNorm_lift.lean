-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_pinch_traceNorm_lift
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.pinch_traceNorm_lift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:39:36.409554+00:00
-- url     : https://prove2.me/theorems/6920c2f2-b2ac-4a1a-8907-34e195d1a048
-- title:
--   Trace-norm lifting through rank-one pinching
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Let $\rho_{AR}$ be a density operator and $\mathcal E(\omega)=\sum_y(P_y\otimes I_R)\omega(P_y\otimes I_R)$ the pinching associated with any complete rank-one basis measurement on $A$. Put $\rho'=\mathcal E(\rho)$. If $\epsilon\ge0$, $\sigma'$ is a normalized density fixed by $\mathcal E$, and $\|\sigma'-\rho'\|_1\le\epsilon$, then there exists a normalized density $\sigma$ satisfying
--
--   $$
--   \|\sigma-\rho\|_1\le2\sqrt\epsilon,\qquad \sigma'=\mathcal E(\sigma).
--   $$
--
--   Both distances use the full trace norm.
--
--   This gives the trace-norm counterpart of the fidelity lifting result.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 26, Corollary 4.14

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 4.14, PDF p.26: full trace-norm lifting with 2 sqrt(eps).
The printed comma in the distance is read as subtraction, and the concluding
prime is retained: sigmaPrime = rankOnePinching U sigma. No assumption eps < 1 is added. -/
theorem pinch_traceNorm_lift {A R : Type} [Fintype A] [Fintype R]
    [DecidableEq A] [DecidableEq R] [Nonempty A] [Nonempty R]
    (rho sigmaPrime : Matrix (A × R) (A × R) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigmaPrime)
    (U : Matrix.unitaryGroup A ℂ) (hblock : sigmaPrime = rankOnePinching U sigmaPrime)
    (eps : ℝ) (heps : 0 ≤ eps) (hclose : traceNorm (sigmaPrime - rankOnePinching U rho) ≤ eps) :
    ∃ sigma : Matrix (A × R) (A × R) ℂ, IsDensityMatrix sigma ∧
      traceNorm (sigma - rho) ≤ 2 * Real.sqrt eps ∧ sigmaPrime = rankOnePinching U sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
