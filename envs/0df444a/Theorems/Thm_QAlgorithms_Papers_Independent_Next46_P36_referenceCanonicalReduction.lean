-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_referenceCanonicalReduction
-- name    : QAlgorithms.Papers.Independent.Next46.P36.referenceCanonicalReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:38:50.955208+00:00
-- url     : https://prove2.me/theorems/2733c68d-b258-49e7-bb89-f9d00caac1a1
-- title:
--   Lemma 1: reference extension and state-dependent canonical reduction
-- statement:
--   Let $U$ be an actual finite-dimensional representation of a compact group with normalized Haar prior and an exhaustive unitary decomposition $H=\bigoplus_{\mu\in S}H_\mu\otimes\mathbb C^{m_\mu}$. The occurring irreducibles are pairwise inequivalent, $S$ is finite and nonempty, and $d_\mu,m_\mu>0$.
--
--   A finite reference dimension can be chosen, and every positive integer $r$ satisfying
--
--   $$d_\mu\le m_\mu r\quad(\mu\in S),\qquad\text{equivalently}\quad r\ge\max_\mu\left\lceil\frac{d_\mu}{m_\mu}\right\rceil,$$
--
--   suffices. For each normalized pure state in $H\otimes\mathbb C^r$, there are an isometry $J:H_{\rm can}\to H\otimes\mathbb C^r$ and a normalized $\phi\in H_{\rm can}$ such that $J\phi=\psi$ and $(U_g\otimes I_r)J=JU_g^{\rm can}$ for every $g$. The isometry is chosen for this state before the unknown $g$. Every measurement transfers in both directions with the same conditional Born probabilities on these orbits. Compression has density $J^\dagger M(\hat g)J$ and the same reference measure.
--
--   For every fixed measurement and integrable average cost, some pure input has risk no larger than any given mixed input. These facts justify the canonical reduction when an external reference is allowed.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 4, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF pp.3-4 Lemma 1: reference extension by r multiplies every physical
multiplicity by r. The integer capacity condition is d_mu <= m_mu*r, equivalently
r >= ceil(d_mu/m_mu), with m_mu positive. The isometry is chosen AFTER the input
state and BEFORE g, and preserves its entire orbit and every measurement law.
The final clause states the pure-input reduction used at the start of III C. -/
theorem referenceCanonicalReduction
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {I S : Type*} [Fintype I] [DecidableEq I]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (U : G → Matrix I I ℂ) (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (B : BasedDecomposition U D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    (∃ r : ℕ, 0 < r ∧ ∀ s, (D s).dim ≤ B.multiplicity s * r) ∧
    (∀ r : ℕ, 0 < r → (∀ s, (D s).dim ≤ B.multiplicity s * r) →
      ∀ psi : EuclideanSpace ℂ (I × Fin r), QAlgorithms.IsState psi →
      ∃ J : Matrix (I × Fin r) (CanonicalIndex D) ℂ,
      ∃ phi : EuclideanSpace ℂ (CanonicalIndex D),
        Jᴴ * J = 1 ∧ QAlgorithms.IsState phi ∧
        WithLp.toLp 2 (J.mulVec (WithLp.ofLp phi)) = psi ∧
        (∀ g, (U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) * J = J * canonicalAction D g) ∧
        (∀ M : QAlgorithms.Measurements.DensityPOVM (I × Fin r) G,
          ∃ L : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G,
            L.reference = M.reference ∧ (∀ h, L.density h = Jᴴ * M.density h * J) ∧
            ∀ g h, QAlgorithms.effectProb (M.density h)
              (QAlgorithms.conjSuperop (U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) (QAlgorithms.pureDensity psi)) =
              QAlgorithms.effectProb (L.density h) (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity phi))) ∧
        (∀ L : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G,
          ∃ M : QAlgorithms.Measurements.DensityPOVM (I × Fin r) G,
            M.reference = L.reference ∧ ∀ g h,
              QAlgorithms.effectProb (M.density h)
                (QAlgorithms.conjSuperop (U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) (QAlgorithms.pureDensity psi)) =
              QAlgorithms.effectProb (L.density h) (QAlgorithms.conjSuperop (canonicalAction D g) (QAlgorithms.pureDensity phi)))) ∧
    (∀ r : ℕ, 0 < r → ∀ cost : G → G → ℝ,
      Measurable (Function.uncurry cost) →
      ∀ rho : Matrix (I × Fin r) (I × Fin r) ℂ,
      ∀ M : QAlgorithms.Measurements.DensityPOVM (I × Fin r) G,
        RepresentationAdmissible (fun g => U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) dg cost rho M →
        ∃ psi : EuclideanSpace ℂ (I × Fin r), QAlgorithms.IsState psi ∧
          RepresentationAdmissible (fun g => U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) dg cost (QAlgorithms.pureDensity psi) M ∧
          representationRisk (fun g => U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) dg cost (QAlgorithms.pureDensity psi) M ≤
            representationRisk (fun g => U g ⊗ₖ (1 : Matrix (Fin r) _ ℂ)) dg cost rho M) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
