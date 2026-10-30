-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cbEntropy_additive
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cbEntropy_additive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:26:54.857398+00:00
-- url     : https://prove2.me/theorems/34acb220-06a0-406c-a8c6-8c2423f9d5c3
-- title:
--   Theorem 3 / (1.2): additivity of minimal CB entropy (original paper seed)
-- statement:
--   Let $\Phi_A:M_{m_A}\to M_{n_A}$ and $\Phi_B:M_{m_B}\to M_{n_B}$ be arbitrary complex-linear completely positive trace-preserving maps between nonzero finite matrix algebras. For a channel $\Phi$ with input dimension $m$, define $S_{\mathrm{CB,min}}(\Phi)$ as the infimum of $S((\mathrm{id}_m\otimes\Phi)(|\psi\rangle\langle\psi|))-S(\operatorname{Tr}_2|\psi\rangle\langle\psi|)$ over all unit vectors $\psi\in\mathbb C^m\otimes\mathbb C^m$, where $S$ is the von Neumann entropy with natural logarithms. Then
--
--   $$S_{\mathrm{CB,min}}(\Phi_A\otimes\Phi_B)=S_{\mathrm{CB,min}}(\Phi_A)+S_{\mathrm{CB,min}}(\Phi_B).$$
--
--   The tensor map acts on both subsystems by its matrix-unit expansion, including entangled inputs. This gives an additive conditional-entropy quantity associated with a channel.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 8, Theorem 3 / (1.2): additivity of minimal CB entropy (original paper seed)

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

/-- Theorem 3 / (1.2), PDF pp.3,8: minimal CB entropy is additive for all CPT pairs. -/
theorem cbEntropy_additive {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (Phi : (Mat A →ₗ[ℂ] Mat B)) (Psi : (Mat C →ₗ[ℂ] Mat D)) (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    minCBEntropy (tensorMap Phi Psi) = minCBEntropy Phi + minCBEntropy Psi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
