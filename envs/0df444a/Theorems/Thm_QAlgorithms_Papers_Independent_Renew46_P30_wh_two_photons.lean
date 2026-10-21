-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_two_photons
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_two_photons
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:21:05.714828+00:00
-- url     : https://prove2.me/theorems/3dbcdc55-cd34-4470-867d-f2a3b703b58a
-- title:
--   §V.B.2(ii): one photon in each mode
-- statement:
--   For two identical displacements on the full two-mode Fock space, use the passive unitary $V$ fixed by the printed generator. Its number-state action has the corrected relative sign
--
--   $$V|1,1\rangle=\frac{|2,0\rangle-|0,2\rangle}{\sqrt2}.$$
--
--   The displayed completed kernel can be written as
--
--   $$\Xi=4|1,1\rangle\langle1,1|+2V^\dagger\bigl(|0\rangle\langle0|\otimes(I-|0\rangle\langle0|-|2\rangle\langle2|)\bigr)V.$$
--
--   It is bounded and positive, its covariant density defines a normalized full-space operator measure, and it attains the maximum likelihood $4$ on $|1,1\rangle$. The universal bound also covers regular generalized seed forms. The source's preceding plus-sign decomposition is corrected without changing this kernel or value.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.2(ii): one photon in each mode

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

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet displacement displacementMatrix coherentMeasure coherentKet)

variable {J : Type*} [DecidableEq J]

/-- PDF p.6, §V.B.2(ii): corrected relative sign dictated by the printed generator;
the displayed full seed is positive, normalized, and attains the maximum 4. -/
theorem wh_two_photons :
    fockConcentration 1 (multiKet (fun _ : Fin 2 => 1)) =
      (1 / Real.sqrt 2 : ℂ) • (multiKet (Fin.cases 2 (fun _ => 0)) -
        multiKet (Fin.cases 0 (fun _ => 2))) ∧
    MultiMaximum (multiKet (fun _ : Fin 2 => 1)) twoPhotonSeed 4 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
