-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_rains_crossEntropy_objective
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.rains_crossEntropy_objective
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:43:05.725418+00:00
-- url     : https://prove2.me/theorems/bdb27cd0-5fcc-48ca-965e-1fcc2ba67ac1
-- title:
--   Rains and natural-log cross-entropy optimization
-- statement:
--   Let $\rho$ be a density operator on nonzero finite-dimensional $A\otimes B$ in fixed product bases. Put $\mathrm{PPT}'=\{\sigma\ge0:\|\sigma^{T_B}\|_1\le1\}$, let $R(\rho)=\inf_{\sigma\in\mathrm{PPT}'}D(\rho\|\sigma)$ use base-two relative entropy, and let $C(\rho)=\inf_{\sigma\in\mathrm{PPT}'}[-\operatorname{Tr}(\rho\ln\sigma)]$. Both objectives take value $+\infty$ on support failure. Then
--
--   $$C(\rho)=\ln(2)R(\rho)+\ln(2)S(\rho).$$
--
--   Moreover, each feasible $\sigma$ minimizes relative entropy if and only if it minimizes cross entropy. Here $S$ is von Neumann entropy in bits. This makes the optimization equivalence in Appendix B precise while retaining the entropy shift and base conversion.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 18, Appendix B, Eq. (69): Rains optimization as natural-log cross entropy

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

/-- Appendix B, arXiv:1706.06221v3, PDF pp.18–19, Eq.(69).
The cross-entropy optimum in nats is ln(2) times R plus entropy in nats;
optimizer equivalence retains the entropy offset and log-base conversion. -/
theorem rains_crossEntropy_objective {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    crossEntropyOptimum rho = (Real.log 2 : EReal) * rains rho +
      (Real.log 2 * vnEntropy rho : EReal) ∧
    (∀ sigma : Matrix (A × B) (A × B) ℂ, pptPrime sigma →
      (relativeEntropy rho sigma = rains rho ↔
        crossEntropy rho sigma = crossEntropyOptimum rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
