-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P05_permutation_pair_spectra
-- name    : QAlgorithms.Papers.Independent.Extend50.P05.permutation_pair_spectra
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:24:32.47432+00:00
-- url     : https://prove2.me/theorems/00dc1dd2-a35a-4c98-b0cc-315a12227485
-- title:
--   Two complete permutation-pair spectra
-- statement:
--   Let $d\ge2$ and use the computational basis $|a,b,c\rangle$ of three qudits. Define $u_i=\sum_a|a,a,i\rangle$, $v_i=\sum_a|a,i,a\rangle$, $A=\sum_i|u_i\rangle\langle u_i|$, $B=\sum_i|v_i\rangle\langle v_i|$ and $R=\sum_i|v_i\rangle\langle u_i|$. Their two complete spectra, with algebraic multiplicities, are
--
--   $$
--   \operatorname{spec}(A+B)=\{(d+1)^{[d]},(d-1)^{[d]},0^{[d^3-2d]}\},
--   \qquad
--   \operatorname{spec}(R+R^*)=\{(d+1)^{[d]},-(d-1)^{[d]},0^{[d^3-2d]}\}.
--   $$
--
--   The Lean statement records the corresponding characteristic-polynomial identities. The cup vectors have squared norm $d$ and inner products $\langle u_i,v_j\rangle=\delta_{ij}$.
--
--   These physical spectra explain the positivity obstruction for the sum of the two three-cycles.
-- source:
--   A geometrical description of the universal $1 \to 2$ asymmetric quantum cloning region, arXiv:2106.09655v1, PDF p. 8, Unnumbered supporting result: two complete nonzero spectra

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P05

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P60 (isotropic)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.8: the two complete spectra, including zero eigenvalues, as characteristic
polynomials. Diagrammatic cups have norm squared d despite the inconsistent normalization prose. -/
theorem permutation_pair_spectra (d : ℕ) (hd : 2 ≤ d) :
    (cupOperatorOne d + cupOperatorTwo d).charpoly =
      (Polynomial.X - Polynomial.C ((d : ℂ) + 1)) ^ d *
      (Polynomial.X - Polynomial.C ((d : ℂ) - 1)) ^ d *
      Polynomial.X ^ (d ^ 3 - 2 * d) ∧
    (cycleOperator d + (cycleOperator d)ᴴ).charpoly =
      (Polynomial.X - Polynomial.C ((d : ℂ) + 1)) ^ d *
      (Polynomial.X + Polynomial.C ((d : ℂ) - 1)) ^ d *
      Polynomial.X ^ (d ^ 3 - 2 * d) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P05

end
