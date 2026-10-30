-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P23_direct_sum_equivalence
-- name    : QAlgorithms.Papers.Independent.Extend50.P23.direct_sum_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:43:15.057146+00:00
-- url     : https://prove2.me/theorems/b33aded8-e550-4eae-abc5-a74535ad2d03
-- title:
--   Equivalence of arbitrary irreducibles by a constructed direct sum
-- statement:
--   Let $\sigma:G\to U(p)$ and $\tau:G\to U(q)$ be any two continuous irreducible representations of a compact Hausdorff group. Let $\mu$ be its normalized regular Borel Haar measure. Construct the continuous unitary representation $\rho=\sigma\oplus\tau$ on $\mathbb C^p\oplus\mathbb C^q$. Draw a fresh GUE matrix $H$ on that direct sum, apply exact Haar averaging, and take the indicated off-diagonal block:
--
--   $$
--   F=\left[\int_G (\sigma(g)\oplus\tau(g))H(\sigma(g)\oplus\tau(g))^\dagger\,d\mu(g)\right]_{12}.
--   $$
--
--   Almost surely, $F=0$ if and only if $\sigma$ and $\tau$ are inequivalent. For every draw with $F\ne0$, $F$ is invertible, $\sigma(g)=F\tau(g)F^{-1}$ for every $g\in G$, and $\alpha F$ is unitary for some nonzero complex scalar $\alpha$.
--
--   Thus the direct sum constructs the common representation required for the equivalence primitive. Equal dimensions are a conclusion of the nonzero case rather than an assumption; no numerical error or runtime guarantee is asserted.
-- source:
--   RepLAB: a computational/numerical approach to representation theory, arXiv:1911.09154v1, PDF p. 6, §2.3, extension of Proposition 1 to arbitrary irreducibles

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P23

open MeasureTheory

open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Support21.P09 (EquivalentModels)

open QAlgorithms.Papers.Independent.Dependency50.P05 (UnitaryBetween)

/-- PDF p.6, §2.3: apply Proposition 1 to the constructed direct sum of any
two continuous complex unitary irreducibles. The off-diagonal block of a fresh
Haar-projected GUE sample decides equivalence almost surely and, when nonzero,
computes the change of basis up to unitary normalization. Dimensions need not
be assumed equal. This is the exact compact-group primitive, not a guarantee
for the 1000-step numerical Haar approximation. -/
theorem direct_sum_equivalence {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [Measure.IsHaarMeasure mu] [Measure.Regular mu]
    [IsProbabilityMeasure mu] {p q : ℕ}
    (sigma : G → Matrix (Fin p) (Fin p) ℂ)
    (tau : G → Matrix (Fin q) (Fin q) ℂ)
    (hsigma : IsUnitaryRepresentation sigma) (htau : IsUnitaryRepresentation tau)
    (hisigma : QAlgorithms.Papers.Independent.Support21.P09.Irreducible sigma) (hitau : QAlgorithms.Papers.Independent.Support21.P09.Irreducible tau) :
    IsUnitaryRepresentation (representationDirectSum sigma tau) ∧
    DetectionLaw sigma tau
      (fun x => (representationHaarProjection (representationDirectSum sigma tau) mu (gueMatrix x)).submatrix
        Sum.inl Sum.inr)
      (gaussianCoordinatesLaw (Fin p ⊕ Fin q)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P23

end
