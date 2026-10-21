-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_depolarizingAssistedCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.depolarizingAssistedCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:28:27.993493+00:00
-- url     : https://prove2.me/theorems/9bf0ab1d-0cc8-44d1-89ef-d3b004e548b5
-- title:
--   Depolarizing assisted capacity and its chaotic-state maximizer
-- statement:
--   Let $d\ge2$, $0\le p\le d^2/(d^2-1)$, and let $\Phi_p(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Put $\bar S=I/d$ and $a=1-p(d^2-1)/d^2$. The normalized input $\bar S$ attains the maximum of $I(S;\Phi_p)$ over all density operators, and $H(\bar S)=H(\Phi_p(\bar S))=\log_2d$. Moreover,
--
--   $$C_{\rm ea}(\Phi_p)=I(\bar S;\Phi_p)=\log_2d^2+a\log_2a+\frac{p(d^2-1)}{d^2}\log_2\frac p{d^2},\qquad C_{\rm ea}(\Phi_p)\le C^{(1)}(\Phi_p)+\log_2d.$$
--
--   Products with zero eigenvalues use $0\log_2 0=0$. This computes a genuine capacity and records its optimizer and the special-case comparison asserted on page 7.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 8, §III, equation (25): depolarizing entanglement-assisted capacity and optimizer

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.8, (25): capacity, maximizing normalized input I/d, and its input/output
entropies. Also includes the depolarizing special-case comparison asserted on p.7. -/
theorem depolarizingAssistedCapacity (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    let N := QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p
    let a := 1 - p * ((d : ℝ)^2 - 1) / (d : ℝ)^2
    IsDensityMatrix (chaotic d) ∧
    IsGreatest {v | ∃ rho : Matrix (Fin d) (Fin d) ℂ,
      IsDensityMatrix rho ∧ v = inputMutualInfo N rho} (inputMutualInfo N (chaotic d)) ∧
    vnEntropy (chaotic d) = Real.logb 2 d ∧
    vnEntropy (N (chaotic d)) = Real.logb 2 d ∧
    regularizedAssistedHolevo N = inputMutualInfo N (chaotic d) ∧
    regularizedAssistedHolevo N = Real.logb 2 ((d : ℝ)^2) + a * Real.logb 2 a +
      (p * ((d : ℝ)^2 - 1) / (d : ℝ)^2) * Real.logb 2 (p / (d : ℝ)^2) ∧
    regularizedAssistedHolevo N ≤ holevoCapacity N + Real.logb 2 d := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
