-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_cartesian_partial_depolarization
-- name    : QAlgorithms.Papers.Independent.Next46.P29.cartesian_partial_depolarization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:23:21.709914+00:00
-- url     : https://prove2.me/theorems/f6fca28e-d36a-45ea-9006-8b4d7402b7d4
-- title:
--   Canonical Cartesian tokens induce partial depolarization
-- statement:
--   Let $L\ge0$ be an integer cutoff. Use the actual SU(2) spin-$j$ representations for every integer $j=0,\ldots,L$, with paired multiplicity spaces of dimensions $2j+1$. Their restricted token dimension is $D_R=\sum_{j=0}^L(2j+1)^2=(2L+1)(2L+3)(L+1)/3$, and the token is $|e_L\rangle=\sum_j\sqrt{(2j+1)/D_R}\sum_{m=-j}^j|j,m\rangle|\phi_{j,m}\rangle$. The message is the actual spin-$1/2$ representation. Let $\mathcal E_L$ be normalized SU(2) Haar encoding and $\mathcal R_L=D_R\mathcal E_L^\dagger$ the fixed covariant recovery. The token is normalized, both maps are channels, and for every qubit density operator,
--
--   $$\mathcal R_L\mathcal E_L(\rho)=\frac{L}{L+1}\rho+\frac{1}{L+1}\frac{I_2}{2}.$$
--
--   No extension to half-integer cutoffs or optimization of token preparation is claimed.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 12, §V.A: Cartesian-token partial depolarization, Eqs.(71)–(72)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.12–14, Eqs.(71)–(72),(92): Cartesian-token partial depolarization.
The overlap and Haar law are normalized by construction; the first integral line
of Eq.(71) is not used as a normalization convention. Printed Eq.(68) omits
`D_R^(-2)` from the squared overlap; the normalized Eq.(60) ket restores it,
and recovery uses `D_R E†` as Eq.(38) requires. Only those inconsistent
intermediate factors are changed; the final Eqs.(72),(92) agree. -/
theorem cartesian_partial_depolarization (L : ℕ) :
    IsState (cartesianKet L) ∧ IsChannel (cartesianEncoding L) ∧
    IsChannel (cartesianRecovery L) ∧
    cartesianDimension L = (2 * L + 1) * (2 * L + 3) * (L + 1) / 3 ∧
    ∀ rho, IsDensityMatrix rho →
      cartesianRecovery L (cartesianEncoding L rho) =
        ((L : ℝ) / (L + 1) : ℂ) • rho +
        ((1 : ℝ) / (L + 1) : ℂ) • mixed (O := Fin 2) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
