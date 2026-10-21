-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_su_two_different
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.su_two_different
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:14:34.131699+00:00
-- url     : https://prove2.me/theorems/d9368b25-637d-41f7-9aa4-e621097f3682
-- title:
--   §V.A.3: two different pure finite-dimensional inputs
-- statement:
--   Let $d\ge2$, and let $\psi,\phi\in\mathbb C^d$ be unit vectors under the action $U\otimes U$ of $SU(d)$ with probability Haar measure. Put $s=|\langle\psi,\phi\rangle|$ and $d_\pm=d(d\pm1)/2$. Their exact optimum is
--
--   $$L_{\max}=\left(\sqrt{d_+(1+s^2)/2}+\sqrt{d_-(1-s^2)/2}\right)^2\le d^2.$$
--
--   The symmetric/antisymmetric canonical seed attains this value; when $s=1$ the absent antisymmetric sector is completed without normalizing a zero vector. If $s^2=1/d$, the factorized normalized seed $d^2|\psi\rangle\langle\psi|\otimes|\phi\rangle\langle\phi|$ attains $d^2$. Every positive full-space normalized seed has trace $d^2$ and likelihood at most $d^2$ on every density input. This isolates the overlap at which a separable optimum reaches the absolute ceiling.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 5, §V.A.3: two different pure finite-dimensional inputs

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

/-- PDF p.5, §V.A.3: exact optimum, the universal d² ceiling, and the factorized
attaining seed at squared overlap 1/d. The canonical seed handles s=1 separately. -/
theorem su_two_different (d : ℕ) (hd : 2 ≤ d) (mu : Measure (SU d))
    [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi phi : EuclideanSpace ℂ (Fin d)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    let s2 := Complex.normSq (inner ℂ psi phi)
    MatrixMaximum mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) (QAlgorithms.tensorVec psi phi) (pairSeed d psi phi)
      (pairFormula d s2) ∧ pairFormula d s2 ≤ (d : ℝ) ^ 2 ∧
    (s2 = (d : ℝ)⁻¹ →
      MatrixMaximum mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) (QAlgorithms.tensorVec psi phi)
        ((d ^ 2 : ℂ) • Matrix.kronecker (QAlgorithms.pureDensity psi) (QAlgorithms.pureDensity phi))
        ((d : ℝ) ^ 2)) ∧
    (∀ Xi : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      Xi.PosSemidef → MatrixNormalized mu (fun g : SU d => pairAction (g : Matrix (Fin d) (Fin d) ℂ)) Xi →
      (Matrix.trace Xi).re = (d : ℝ) ^ 2 ∧
      ∀ rho, QAlgorithms.IsDensityMatrix rho →
        QAlgorithms.effectProb Xi rho ≤ (d : ℝ) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
