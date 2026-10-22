-- Prove2me | Theorems.Thm_RandomGateDesign_MasterBound_fact_2
-- name    : RandomGateDesign.MasterBound.fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:18.791964+00:00
-- url     : https://prove2.me/theorems/d3c20518-b181-4d0d-8634-e322dd769bc2
-- title:
--   Fact 2 — non-Hermitian matrix master bound
-- statement:
--   Let $X_1,\ldots,X_N$ be independent measurable random complex $m\times m$ matrices on a probability space, with $m>0$. Write $H(A)=\begin{psmallmatrix}0&A\\A^*&0\end{psmallmatrix}$ for the Hermitian dilation. If $\theta>0$ and each $e^{\theta H(X_k)}$ is integrable, then for any real $\delta$,
--
--   $$\Pr\!\left(\left\|\sum_{k=1}^{N}X_k\right\|\ge\delta\right)\le e^{-\theta\delta}\operatorname{tr}\exp\!\left(\sum_{k=1}^{N}\log\mathbb E e^{\theta H(X_k)}\right).$$
--
--   This pointwise form in $\theta$ is equivalent to the paper's infimum over positive $\theta$ and supplies the concentration step for Theorem 18. The norm is the spectral operator norm.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, p. 6, Fact 2

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RandomGateDesign.MasterBound

theorem fact_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m N : ℕ} [NeZero m]
    (X : Fin N → Ω → Matrix (Fin m) (Fin m) ℂ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X P)
    (θ δ : ℝ) (hθ : 0 < θ)
    (hint : ∀ k, Integrable
      (fun ω => TroppMatrixConcentration.matrixExp
        (θ • TroppMatrixConcentration.dilation (X k ω))) P) :
    (P {ω | δ ≤ TroppMatrixConcentration.spectralNorm (∑ k, X k ω)}).toReal ≤
      Real.exp (-θ * δ) *
        TroppMatrixConcentration.traceExp
          (TroppMatrixConcentration.cumulantSum P
            (fun k ω => TroppMatrixConcentration.dilation (X k ω)) θ) := by sorry

end RandomGateDesign.MasterBound
