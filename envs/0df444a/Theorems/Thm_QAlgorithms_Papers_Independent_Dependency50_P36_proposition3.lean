-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_proposition3
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.proposition3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:32:58.111106+00:00
-- url     : https://prove2.me/theorems/f50d87cf-7a0b-41b8-abef-65776b8a5c05
-- title:
--   PPT one-shot distillation: attained SDP and integer rounding
-- statement:
--   Let $\rho$ be a density operator on nonzero finite-dimensional complex spaces $A\otimes B$, with fixed product bases, and let $0\le\varepsilon<1$. A PPT operation means a completely PPT-preserving CPTP map. Write $T_B$ for Bob's partial transpose and $E_{D,\mathrm{PPT}}^{(1),\varepsilon}$ for the base-two logarithm of the largest positive integer rank whose maximally entangled target has optimal squared fidelity at least $1-\varepsilon$. The minimum
--
--   $$
--   \eta_0=\min\{\eta:\exists M,\ 0\le M\le I,\ \operatorname{Tr}(\rho M)\ge1-\varepsilon,\ -\eta I\le M^{T_B}\le\eta I\}
--   $$
--
--   is attained and positive, and
--
--   $$E_{D,\mathrm{PPT}}^{(1),\varepsilon}(\rho)=\log_2\lfloor1/\eta_0\rfloor.$$
--
--   This separates the semidefinite optimization from its nonlinear integer-rank postprocessing.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 4, Proposition 3; Eq. (7), with SDP implementation Eq. (24)

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

/-- Proposition 3, arXiv:1706.06221v3, PDF pp.4–5, Eqs.(7),(24).
The SDP minimum is attained and positive; reciprocal/floor/log are postprocessing. -/
theorem proposition3 {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    ∃ eta : ℝ, ∃ M : Matrix (A × B) (A × B) ℂ,
      0 < eta ∧ pptSDPFeasible rho epsilon eta M ∧
      (∀ z : ℝ, ∀ N : Matrix (A × B) (A × B) ℂ,
        pptSDPFeasible rho epsilon z N → eta ≤ z) ∧
      oneShot .ppt rho epsilon = (log2 (Nat.floor eta⁻¹) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
