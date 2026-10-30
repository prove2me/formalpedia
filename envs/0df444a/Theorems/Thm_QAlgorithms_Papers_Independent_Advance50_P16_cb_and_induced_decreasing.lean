-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cb_and_induced_decreasing
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cb_and_induced_decreasing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:37:58.395955+00:00
-- url     : https://prove2.me/theorems/85ee3d42-59fa-4669-9ea7-9e33c4fe5738
-- title:
--   Theorem 13(a–c): CB equals induced norm and both are multiplicative for q >= p
-- statement:
--   Let $1\le p\le q\le\infty$, and let $\Phi_A,\Phi_B$ be arbitrary complex-linear CP maps between nonzero finite matrix algebras. For each factor $\Phi$, the CB, full induced, and positive induced norms coincide. Both norms are multiplicative:
--
--   $$\|\Phi\|_{\mathrm{CB},q\to p}=\|\Phi\|_{q\to p}=\|\Phi\|^+_{q\to p},$$
--   $$\|\Phi_A\otimes\Phi_B\|_{q\to p}=\|\Phi_A\|_{q\to p}\|\Phi_B\|_{q\to p},\qquad
--   \|\Phi_A\otimes\Phi_B\|_{\mathrm{CB},q\to p}=\|\Phi_A\|_{\mathrm{CB},q\to p}\|\Phi_B\|_{\mathrm{CB},q\to p}.$$
--
--   No trace preservation or assumed CB finiteness is required; finiteness follows from equality with the finite-dimensional induced norm. CB amplification uses outer exponent $p$ on domain and range. These are all three parts of Theorem 13.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 21, Theorem 13(a–c): CB equals induced norm and both are multiplicative for q >= p

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Theorem 13(a–c), PDF pp.21–22: CB equals the positive and full induced norm,
and both kinds of norm are multiplicative. No TP or assumed CB finiteness is added. -/
theorem cb_and_induced_decreasing {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (q p : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q)
    (Phi : (Mat A →ₗ[ℂ] Mat B)) (Psi : (Mat C →ₗ[ℂ] Mat D))
    (hPhi : Entanglement.IsCompletelyPositive Phi) (hPsi : Entanglement.IsCompletelyPositive Psi) :
    (cbSize q p Phi = inducedSize q p Phi ∧ inducedSize q p Phi = positiveInducedSize q p Phi) ∧
    (cbSize q p Psi = inducedSize q p Psi ∧ inducedSize q p Psi = positiveInducedSize q p Psi) ∧
    inducedSize q p (tensorMap Phi Psi) = inducedSize q p Phi * inducedSize q p Psi ∧
    cbSize q p (tensorMap Phi Psi) = cbSize q p Phi * cbSize q p Psi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
