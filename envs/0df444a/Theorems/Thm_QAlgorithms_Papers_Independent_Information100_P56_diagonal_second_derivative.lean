-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_diagonal_second_derivative
-- name    : QAlgorithms.Papers.Independent.Information100.P56.diagonal_second_derivative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:28:48.758532+00:00
-- url     : https://prove2.me/theorems/c3ffc5d7-6bac-4067-b278-2f982f421f2a
-- title:
--   Lemma VIII.2: second derivative of the diagonal-line entropy difference
-- statement:
--   Fix $0<p<1/2$. Put $a=1-2p$, $u=a^2$, $k=1-u$, $t=z^2$ and $r=\sqrt{u+kt}$. Define $\Delta(z)=h((1+az)/2)-h((1+r)/2)$, where $h$ is natural binary entropy. For $|z|<1$,
--
--   $$\Delta''(z)=-\frac u{1-ut}+\frac{ku\operatorname{atanh}r}{r^3}+\frac{k^2t}{r^2(1-r^2)}.$$
--
--   All auxiliary parameters are these constructed expressions. The strict domain ensures nonzero denominators, including at $z=0$. This is the second derivative for the diagonal parameter line.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 23, Lemma VIII.2: second derivative of the diagonal-line entropy difference

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma VIII.2, p.23, Eq.(80): all parameters are constructed from p and z.
The strict domain gives r>0, 1-r^2>0 and 1-u*t>0, including at z=0. -/
theorem diagonal_second_derivative (p z : ℝ) (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    let a := 1 - 2 * p
    let u := a ^ 2
    let k := 1 - u
    let t := z ^ 2
    let r := Real.sqrt (u + k * t)
    HasDerivAt (deriv (diagonalDelta p))
      (-u / (1 - u * t) + k * u * inverseTanh r / r ^ 3 +
        k ^ 2 * t / (r ^ 2 * (1 - r ^ 2))) z := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
