-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq24
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq24
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:42:12.665147+00:00
-- url     : https://prove2.me/theorems/4cbb7621-d9bc-4539-b41f-449d3d5ca39f
-- title:
--   eq24
-- statement:
--   Let $H$ be Hermitian on a positive finite-dimensional space, let $T>0$ be finite, and set $\rho_T=e^{-H/T}/\operatorname{tr}(e^{-H/T})$ and $E(T)=\operatorname{tr}(H\rho_T)$, with Boltzmann constant one. The energy is differentiable and
--
--   $$E'(T)=\operatorname{var}_{\rho_T}(H/T)=\frac{\operatorname{var}_{\rho_T}(H)}{T^2}=\operatorname{var}_{\rho_T}(-\log\rho_T).$$
--
--   Here observable variance is $\operatorname{tr}(\rho A^2)-\operatorname{tr}(\rho A)^2$. Every full-rank density matrix $\rho$ equals the thermal state of $H=-\log\rho$ at temperature one. Heat capacity is defined as the energy derivative; the displayed variance identity is a conclusion.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 9, eq24

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eq. (24), PDF p.9: the derivative identity at strictly positive finite temperature. -/
theorem eq24 {d : ℕ} (hd : 0 < d) (h : Matrix (Fin d) (Fin d) ℂ)
    (hh : h.IsHermitian) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (thermalExpectedEnergy h) (stateObservableVariance (thermalFinite h t) (((t : ℂ)⁻¹) • h)) t ∧
    deriv (thermalExpectedEnergy h) t = stateObservableVariance (thermalFinite h t) (((t : ℂ)⁻¹) • h) ∧
    deriv (thermalExpectedEnergy h) t = stateObservableVariance (thermalFinite h t) h / t ^ 2 ∧
    deriv (thermalExpectedEnergy h) t = surprisalVariance (thermalFinite h t) ∧
    (∀ a : EntropyState d, fullRank a.val → thermalFinite (-cfc Real.log a.val) 1 = a.val) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
