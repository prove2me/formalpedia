-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_depolarizingHolevoCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.depolarizingHolevoCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:28:53.955488+00:00
-- url     : https://prove2.me/theorems/9f34c9a1-ab03-4469-be5a-0da1a5209683
-- title:
--   Depolarizing one-shot Holevo capacity with a uniform basis ensemble
-- statement:
--   Let $d\ge2$, $0\le p\le d^2/(d^2-1)$, and let $\Phi_p(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$. Put $b=1-p(d-1)/d$. The one-shot unassisted Holevo capacity, in bits, is
--
--   $$C^{(1)}(\Phi_p)=\log_2d+b\log_2b+\frac{p(d-1)}d\log_2\frac pd.$$
--
--   For every orthonormal basis, the ensemble of its $d$ pure states with equal probabilities $1/d$ attains this value. Zero logarithmic products have their continuous value zero. This is a one-shot assertion; it does not identify $C^{(1)}$ with regularized $C$.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 8, §III, equation (26): depolarizing one-shot classical capacity and attaining ensemble

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.8, (26): single-use unassisted Holevo capacity, attained by the uniform
ensemble of any orthonormal basis. No additivity or C=C^(1) is asserted. -/
theorem depolarizingHolevoCapacity (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    let N := QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p
    let b := 1 - p * ((d : ℝ) - 1) / d
    holevoCapacity N = Real.logb 2 d + b * Real.logb 2 b +
      (p * ((d : ℝ) - 1) / d) * Real.logb 2 (p / d) ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ, basisHolevo (by omega) p U = holevoCapacity N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
