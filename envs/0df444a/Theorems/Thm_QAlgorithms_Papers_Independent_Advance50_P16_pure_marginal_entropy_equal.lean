-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_pure_marginal_entropy_equal
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.pure_marginal_entropy_equal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:42:51.791237+00:00
-- url     : https://prove2.me/theorems/8f27285b-ed55-4359-873e-70f20cfa689f
-- title:
--   Corollary 19: equal marginal entropies of a bipartite pure state, including infinite dimension
-- statement:
--   Let $\psi$ be a unit vector in an arbitrary completed complex Hilbert tensor product $H_A\widehat\otimes H_B$. Let $\gamma_A=\operatorname{Tr}_B|\psi\rangle\langle\psi|$ and $\gamma_B=\operatorname{Tr}_A|\psi\rangle\langle\psi|$. Then
--
--   $$S(\gamma_A)=S(\gamma_B).$$
--
--   Both sides are extended nonnegative entropies and may equal $+\infty$. Orthonormal-coordinate Hilbert spaces with arbitrary, possibly uncountable, basis index sets model the ambient factors; a unit vector has countable support. The reduced densities are computed by convergent partial-trace series and entropy by the accepted finite-compression supremum. No finite-dimensional or finite-entropy restriction is imposed. This is the complementary-entropy identity for pure states in full Hilbert-space generality.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 33, Corollary 19: equal marginal entropies of a bipartite pure state, including infinite dimension

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

/-- Corollary 19, PDF p.33: arbitrary completed Hilbert tensor products in
orthonormal coordinates, with possibly uncountable ambient bases and infinite entropy.
The extended entropy is the accepted finite-compression entropy; no real infinity conversion. -/
theorem pure_marginal_entropy_equal {A B : Type}
    (psi : QAlgorithms.RealRegisters.Hilbert (A × B)) (hpsi : ‖psi‖ = 1) :
    QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy
      (QAlgorithms.Papers.Independent.Frontier18.P01.traceSecond
        (QAlgorithms.Papers.Independent.Dependency50.P33.rankOne psi)) =
    QAlgorithms.Papers.Independent.Frontier18.P01.homogeneousEntropy
      (QAlgorithms.Papers.Independent.Frontier18.P01.traceFirst
        (QAlgorithms.Papers.Independent.Dependency50.P33.rankOne psi)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
