-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundAlickiFannes
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.backgroundAlickiFannes
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:38:48.892036+00:00
-- url     : https://prove2.me/theorems/9c8bc83d-29da-4873-817d-ca865215849f
-- title:
--   The conditional-entropy continuity bound used in Eq.8
-- statement:
--   Let $\rho_{AB},\sigma_{AB}$ be density operators on nonzero finite-dimensional systems and let $\delta=\tfrac12\|\rho-\sigma\|_1<\tfrac12$. For conditional entropy $H(A|B)_\tau=H(\tau_{AB})-H(\tau_B)$ in bits,
--
--   $$|H(A|B)_\rho-H(A|B)_\sigma|\le8\delta\log_2\dim A-4\delta\log_2(2\delta)-2(1-2\delta)\log_2(1-2\delta).$$
--
--   Products $x\log_2x$ take their continuous zero value. This is the definite cited continuity statement used on p.3; reference [1], Theorem Eq.1, uses the full trace norm $2\delta<1$. The recovery consequence (8), including its boundary case, remains in the separate converse-recovery item.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 3, BackgroundAlickiFannes

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Alicki–Fannes continuity used on PDF p.3 to obtain Eq.8. Reference [1],
arXiv:quant-ph/0312081v2, Theorem Eq.1, PDF p.2, has epsilon equal to the
FULL trace norm. Here delta is half that norm on the two density inputs. -/
theorem backgroundAlickiFannes {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Op (A × B)) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hd : generalizedTraceDistance rho sigma < 1/2) :
    let delta := generalizedTraceDistance rho sigma
    |(vnEntropy rho - vnEntropy (traceLeft rho)) -
      (vnEntropy sigma - vnEntropy (traceLeft sigma))| ≤
      8 * delta * Real.logb 2 (Fintype.card A : ℝ) -
      4 * delta * Real.logb 2 (2*delta) -
      2 * (1-2*delta) * Real.logb 2 (1-2*delta) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
