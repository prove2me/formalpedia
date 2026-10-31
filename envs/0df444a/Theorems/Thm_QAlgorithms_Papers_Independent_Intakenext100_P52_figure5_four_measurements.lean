-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_figure5_four_measurements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.figure5_four_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:39:38.129046+00:00
-- url     : https://prove2.me/theorems/4a692b63-e477-4325-986e-f8128a60bdad
-- title:
--   §5 Figure 5: four measurements for one-qubit U
-- statement:
--   Let $|\psi\rangle$ be normalized and set $U=R_x(\zeta)R_z(\eta)R_x(\xi)$, with $R_a(\theta)=e^{-i\theta\sigma_a}$ and real $\xi,\eta,\zeta$. Put the input on site $1$ of a five-site row, prepare the other four sites in $|+\rangle$, and apply all nearest-neighbour $CZ$s. Measure sites $1,2,3,4$ with outcomes $s_1,s_2,s_3,s_4$ in bases $X$, $M(-2\xi(-1)^{s_1})$, $M(-2\eta(-1)^{s_2})$, $M(-2\zeta(-1)^{s_1+s_3})$. For its physical surviving vector $b_s$,
--
--   $$ |b_s\rangle\langle b_s|=\frac1{16}|\chi_s\rangle\langle\chi_s|,\quad\|b_s\|^2=\frac1{16},\quad |\chi_s\rangle=X^{s_2\oplus s_4}Z^{s_1\oplus s_3}U|\psi\rangle. $$
--
--   **Source correction:** the three nonzero printed angles lack the factor two required by the p.5 rotation convention. Densities discard overall phases; every adaptive basis uses only earlier recorded bits.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 9, §5 Figure 5: four measurements for one-qubit U

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Figure 5, PDF p.9. Printed angles -xi,-eta,-zeta implement half the
claimed rotations under the p.5 definition. Changed to -2xi,-2eta,-2zeta
with the same adaptive signs; densities discard the harmless overall phase.
No Euler-decomposition hypothesis is used to assume the branch conclusion. -/
theorem figure5_four_measurements (xi eta zeta : ℝ) (psi : Vec Bool)
    (hpsi : IsState psi) (s : Fin 4 → Bool) :
    let b := lineBranch 4 (figure5Angles xi eta zeta s) s psi
    let target := act (pauliByproduct (xor (s 1) (s 3)) (xor (s 0) (s 2)) *
      (rx zeta * rz eta * rx xi)) psi
    pureDensity b = (1 / 16 : ℝ) • pureDensity target ∧ ‖b‖ ^ 2 = (1 / 16 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
