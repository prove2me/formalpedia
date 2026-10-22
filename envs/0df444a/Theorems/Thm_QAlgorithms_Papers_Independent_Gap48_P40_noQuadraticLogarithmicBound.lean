-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_noQuadraticLogarithmicBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.noQuadraticLogarithmicBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:22:50.181771+00:00
-- url     : https://prove2.me/theorems/cd03ff13-4486-418b-bf32-44cf82c0617e
-- title:
--   §V.C, Proposition 1: no universal quadratic-logarithmic bound
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. For every real $r>0$, there are $p\in[0,1]$ and $q\in(0,1/2)$ such that the commuting qubit states $\rho=\operatorname{diag}(p,1-p)$ and $\sigma=\operatorname{diag}(q,1-q)$ satisfy
--
--   $$
--   D(\rho\|\sigma)>r\operatorname{Tr}[(\rho-\sigma)^2]\,|\log\lambda_{\min}(\sigma)|.
--   $$
--
--   Thus no universal positive constant gives the proposed quadratic-logarithmic bound.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 5, §V.C, Proposition 1: no universal quadratic-logarithmic bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.5, Proposition 1: commuting qubit witnesses disprove every positive
universal quadratic-logarithmic constant. The proof's (2-p-q)^2 typo is not used. -/
theorem noQuadraticLogarithmicBound (r : ℝ) (hr : 0 < r) :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 < q ∧ q < 1 / 2 ∧
      let rho : Mat 2 := Matrix.diagonal ![(p : ℂ), ((1 - p : ℝ) : ℂ)]
      let sigma : Mat 2 := Matrix.diagonal ![(q : ℂ), ((1 - q : ℝ) : ℂ)]
      relativeEntropy rho sigma >
        ((r * ((rho - sigma) ^ 2).trace.re * |Real.log (minEigenvalue sigma)| : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
