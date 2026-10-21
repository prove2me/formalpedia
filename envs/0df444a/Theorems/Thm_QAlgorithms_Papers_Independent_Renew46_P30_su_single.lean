-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_su_single
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.su_single
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:12:39.895187+00:00
-- url     : https://prove2.me/theorems/04f15334-543f-442b-848e-6b36e420d757
-- title:
--   §V.A.1: single pure-state SU(d) estimation
-- statement:
--   Let $d\ge1$, let $\psi\in\mathbb C^d$ be a unit vector, and use the defining action of $SU(d)$ with probability Haar measure and the induced ray-orbit measure. The seed
--
--   $$\Xi=d|\psi\rangle\langle\psi|$$
--
--   is positive, normalized, and commutes with the ray stabilizer. It attains likelihood $d$, and every normalized positive covariant seed has likelihood at most $d$. This identifies the exact single-copy pure-state estimation optimum.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 5, §V.A.1: single pure-state SU(d) estimation

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

/-- PDF p.5, §V.A.1: one pure state under the defining SU(d) action. -/
theorem su_single (d : ℕ) (hd : 0 < d) (mu : Measure (SU d))
    [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi : EuclideanSpace ℂ (Fin d)) (hn : ‖psi‖ = 1) :
    MatrixMaximum mu (fun g : SU d => (g : Matrix (Fin d) (Fin d) ℂ)) psi
      ((d : ℂ) • QAlgorithms.pureDensity psi) d := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
