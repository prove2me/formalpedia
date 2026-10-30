-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_commutative_measurements_individual
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.commutative_measurements_individual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:27:36.7756+00:00
-- url     : https://prove2.me/theorems/2cebbc76-a1ed-47b4-a568-734b038f835a
-- title:
--   Proposition 9: commutative locally symmetric measurements are individual measurements
-- statement:
--   Let $\mathcal A$ be a commutative unital adjoint-closed algebra on $\mathbb C^d$, $d,n\ge1$. There is a joint spectral PVM $\{E_j\}$ spanning $\mathcal A$, chosen before the POVM to simulate. Every arbitrary-outcome normalized POVM $M$ with local $G_{\mathcal A}$ symmetry has probability laws $K_z$ such that
--   $$M(B)=\sum_{z\in\{1,\ldots,r\}^n}K_z(B)\bigotimes_{i=1}^n E_{z_i}$$
--   for every measurable event $B$. The projectors may have rank greater than one. Thus individual generator measurements followed by stochastic classical processing suffice on every input state.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 14, Proposition 9: commutative locally symmetric measurements are individual measurements

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.14, Proposition 9: a single spectral measurement of generators
on each qudit, followed by stochastic classical processing, reproduces the POVM. -/
theorem commutative_measurements_individual [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) (A : StarSubalgebra ℂ (Mat I))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y = Y * X) :
    ∃ E : GeneratorSpectralPVM A,
      ∀ M : Measurements.OperatorPOVM (Fin n → I) O,
        InAlgebra M.operator (Set.centralizer (localSet n (unitaryCentralizer (A : Set (Mat I))))) →
        ∃ K : (Fin n → Fin E.count) → Measure O, Postprocess E K M.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
