-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_hexagonal_gaussian_logical_noise
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.hexagonal_gaussian_logical_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:10:45.955546+00:00
-- url     : https://prove2.me/theorems/e41962a6-6e1c-4fef-a2ed-e9ded49e0887
-- title:
--   §VIII (96): hexagonal-code logical noise bound
-- statement:
--   Let $\sigma>0$ and use ideal nearest-cell decoding for the hexagonal oscillator qubit. Choose any nearest physical dual-lattice point, and reduce its two integer labels modulo two; even/even labels are stabilizers. A nearest point exists for every displacement. The four Gaussian cell-mass probabilities are nonnegative, integrable, and sum to one; all three nonidentity Pauli probabilities are equal. With $r=\sqrt{\pi/(2\sqrt3)}$, their total satisfies
--
--   $$p_{e,\mathrm{total}}<1-\frac{12}{2\pi\sigma^2}\int_0^r\int_0^{x/\sqrt3}e^{-(x^2+y^2)/(2\sigma^2)}\,dy\,dx.$$
--
--   Ties occur only on cell boundaries, of Gaussian measure zero. Outside-cell mass is not declared equal to logical error, because some larger lattice translations are harmless.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 11, §VIII (96): hexagonal-code logical noise bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section VIII (96), PDF pp.11–12: isotropic hexagonal logical noise and the strict cell bound.
Outside-cell mass is an upper bound, since some larger displacements are stabilizers. -/
theorem hexagonal_gaussian_logical_noise (sigma : ℝ) (hs : 0 < sigma) :
    (∀ x : ℝ × ℝ, ∀ w : ℤ × ℤ,
      planeNorm (x - physicalHex (hexNearest x)) ≤ planeNorm (x - physicalHex w)) ∧
    (∀ a b : Fin 2, Integrable (fun x : ℝ × ℝ =>
      if (hexNearest x).1 % 2 = (a.val : ℤ) ∧ (hexNearest x).2 % 2 = (b.val : ℤ)
        then quadratureGaussianDensity sigma x.1 * quadratureGaussianDensity sigma x.2 else 0) volume) ∧
    (∀ a b : Fin 2, 0 ≤ hexProbability sigma a b) ∧
    (∑ a : Fin 2, ∑ b : Fin 2, hexProbability sigma a b) = 1 ∧
    hexProbability sigma 1 0 = hexProbability sigma 0 1 ∧
    hexProbability sigma 1 0 = hexProbability sigma 1 1 ∧
    (hexProbability sigma 1 0 + hexProbability sigma 0 1 + hexProbability sigma 1 1) <
      1 - 12 / (2 * Real.pi * sigma ^ 2) *
        ∫ x in Set.Icc 0 (Real.sqrt (Real.pi / (2 * Real.sqrt 3))),
          ∫ y in Set.Icc 0 (x / Real.sqrt 3),
            Real.exp (-(x ^ 2 + y ^ 2) / (2 * sigma ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
