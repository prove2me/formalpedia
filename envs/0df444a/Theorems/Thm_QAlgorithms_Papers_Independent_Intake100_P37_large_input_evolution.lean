-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_large_input_evolution
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.large_input_evolution
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:11:12.681336+00:00
-- url     : https://prove2.me/theorems/4acc9d00-edcc-4f58-aa8d-6e1b34e2a629
-- title:
--   Exact solution of the leading large-input transfer model
-- statement:
--   Let $A\ge0$, $m\ge1$, and $\gamma,t\in\mathbb R$. Replace the factors $m+l+1,m+l+2$ in the exact recurrence by $m$, obtaining the separate leading generator $K^{(0)}$ with adjacent entries $\gamma\sqrt m\sqrt{(l+1)(A-l)}$. Its exact exponential coefficients are
--
--   $$
--   (e^{-itK^{(0)}})_{l0}=(-i)^l\sqrt{\binom Al}
--   \cos^{A-l}(\gamma\sqrt m\,t)\sin^l(\gamma\sqrt m\,t),\qquad 0\le l\le A.
--   $$
--
--   The asymptotic meaning of this replacement is fixed by the exact generator $K_{A,n}$: for fixed $A,\gamma$ and every pair of finite sector indices $k,l$,
--
--   $$
--   \lim_{n\to\infty}n^{-1/2}(K_{A,n})_{kl}=(K^{(0)}_{A,1})_{kl}.
--   $$
--
--   Thus (B2) is exact for the explicitly specified (B1) model. This does not assert convergence of the rapidly oscillating exact finite-input evolution at fixed unscaled time or an unprinted state-error rate. When $A=0$ there is a single coefficient equal to one.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 9, Appendix B, Eqs.(B1)-(B2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9-10 Eqs.(B1),(B2): B2 exactly exponentiates the specified leading
model. Fixed-A convergence of the RESCALED generator pins the large-m reading;
no fixed-time convergence of the rapidly oscillating physical evolution is asserted. -/
theorem large_input_evolution (A m : ℕ) (hm : 1 ≤ m) (gamma t : ℝ) :
    (∀ l : Fin (A + 1), leadingAmplitude A m gamma t l =
      (-Complex.I) ^ l.val * (Real.sqrt (Nat.choose A l.val : ℝ) : ℂ) *
        (Real.cos (gamma * Real.sqrt m * t) : ℂ) ^ (A - l.val) *
        (Real.sin (gamma * Real.sqrt m * t) : ℂ) ^ l.val) ∧
    (∀ k l : Fin (A + 1),
      Filter.Tendsto
        (fun n : ℕ => ((Real.sqrt n : ℂ)⁻¹) * emissionTransfer A n gamma k l)
        Filter.atTop (nhds (leadingTransfer A 1 gamma k l))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
