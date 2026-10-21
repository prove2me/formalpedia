-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_blockNormalization
-- name    : QAlgorithms.Papers.Independent.Next46.P36.blockNormalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:40:39.569143+00:00
-- url     : https://prove2.me/theorems/33edc9d2-78c4-449c-a7d8-f9f02d148cf2
-- title:
--   Lemma 3: both block normalization identities
-- statement:
--   Let $G$ be compact with normalized Haar measure and let the finite canonical action have positive-dimensional pairwise inequivalent unitary irreducible blocks. Fix block unitaries $W_\mu$ and the action $V_g$ of Eq. (29). Suppose $\Xi$ is a normalized covariant seed commuting with $U_gV_g$ for every $g$. For any finite dyadic decomposition
--
--   $$\Xi=\sum_i|\eta_i\rangle\langle\eta_i|,\qquad \eta_i=\bigoplus_\mu\sqrt{d_\mu}\operatorname{vec}(A_{i\mu}),$$
--
--   both identities hold:
--
--   $$\sum_i A_{i\mu}^\dagger A_{i\mu}=I_{d_\mu},\qquad\sum_i A_{i\mu}A_{i\mu}^\dagger=I_{d_\mu}\quad(\mu\in S).$$
--
--   The vectors need not be normalized; spectral weights are absorbed in them. These two identities are the normalization constraints used in the optimality bound.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 6, Lemma 3, Eqs. (34)-(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.6 Lemma 3: BOTH Eqs.(34),(35), for every dyadic decomposition (33).
The commutator is with the joint product U_g V_g, not either action separately. -/
theorem blockNormalization
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ)
    {r : ℕ} (A : Fin r → ∀ s, Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ)
    (hN : NormalizedSeed D dg (componentSeed D A))
    (hcomm : ∀ g, componentSeed D A * (canonicalAction D g * rightAction D W g) =
      (canonicalAction D g * rightAction D W g) * componentSeed D A) :
    (∀ s, (∑ i, (A i s)ᴴ * A i s) = 1) ∧
    (∀ s, (∑ i, A i s * (A i s)ᴴ) = 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
