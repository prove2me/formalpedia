-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cb_multiplicative_increasing
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cb_multiplicative_increasing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:36:33.86103+00:00
-- url     : https://prove2.me/theorems/6c952318-0725-467c-90b2-32843d9bda22
-- title:
--   Theorem 11: CB multiplicativity for q <= p
-- statement:
--   Let $1\le q\le p\le\infty$. Let $\Phi_A:M_{m_A}\to M_{n_A}$ and $\Phi_B:M_{m_B}\to M_{n_B}$ be complex-linear CP maps on nonzero finite matrix algebras, and assume their CB $q\to p$ norms are finite. Then
--
--   $$\|\Phi_A\otimes\Phi_B\|_{\mathrm{CB},q\to p}=\|\Phi_A\|_{\mathrm{CB},q\to p}\,\|\Phi_B\|_{\mathrm{CB},q\to p}.$$
--
--   CB norms are extended suprema over all positive finite ancillary dimensions, using outer exponent $\min(p,q)=q$ on both sides of each amplification. No optimizing ancilla is asserted. This is the multiplicativity result underlying CB-entropy additivity.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 19, Theorem 11: CB multiplicativity for q <= p

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

/-- Theorem 11 / (4.1), PDF pp.19–20: CP and CB are retained separately.
There is no assertion of a maximizing ancillary dimension. -/
theorem cb_multiplicative_increasing {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (q p : ℝ≥0∞) (hq : 1 ≤ q) (hqp : q ≤ p)
    (Phi : (Mat A →ₗ[ℂ] Mat B)) (Psi : (Mat C →ₗ[ℂ] Mat D))
    (hPhi : Entanglement.IsCompletelyPositive Phi) (hPsi : Entanglement.IsCompletelyPositive Psi)
    (hPhiCB : cbSize q p Phi < ⊤) (hPsiCB : cbSize q p Psi < ⊤) :
    cbSize q p (tensorMap Phi Psi) = cbSize q p Phi * cbSize q p Psi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
