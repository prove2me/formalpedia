-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_coherent_identical
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_coherent_identical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:17:51.304736+00:00
-- url     : https://prove2.me/theorems/9df62f5a-1189-4b5c-8ff3-baf6dd5cff7b
-- title:
--   §V.B.2(i): N identical coherent displacements
-- statement:
--   Let $N=r+1>1$, with full oscillator Fock space and reference measure $d^2z/\pi$. The concentration unitary fixes $|0\rangle^{\otimes N}$, and identical displacements generate the coherent orbit $|z\rangle^{\otimes N}$ with its actual product coherent coefficients. A full positive normalized bounded seed exists whose compression to the occupied irreducible subspace is $N|0^N\rangle\langle0^N|$, and
--
--   $$L_{\max}=N.$$
--
--   The explicit completion is the number-product construction at total occupation zero. Its normalized operator measure attains the bound against bounded and regular generalized covariant kernels. The rank-one compression alone is not used as a full-space POVM.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.2(i): N identical coherent displacements

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

/-- PDF p.6, §V.B.2(i): N identical coherent inputs, actual vacuum-preserving concentration
and a full-space normalized completion, attaining N. -/
theorem wh_coherent_identical (r : ℕ) (hr : 0 < r) :
    let vacuum : MultiFock (r + 1) := multiKet (fun _ => 0)
    fockConcentration r vacuum = vacuum ∧
    MultiMaximum vacuum (numberSeed r (fun _ => 0)) (r + 1) ∧
    (∀ z : ℂ, ∀ m : Fin (r + 1) → ℕ,
      multiDisplacement (fun _ => z) vacuum m =
        ∏ j, QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient z (m j)) ∧
    ∀ v w : MultiFock (r + 1),
      v ∈ oscillatorComponent r (multiKet (fun _ => 0)) →
      w ∈ oscillatorComponent r (multiKet (fun _ => 0)) →
      inner ℂ v (numberSeed r (fun _ => 0) w) =
        inner ℂ v ((((r + 1 : ℕ) : ℂ) • InnerProductSpace.rankOne ℂ vacuum vacuum) w) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
