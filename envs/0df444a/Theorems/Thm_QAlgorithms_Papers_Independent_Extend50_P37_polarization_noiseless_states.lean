-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_polarization_noiseless_states
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.polarization_noiseless_states
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:25:35.251398+00:00
-- url     : https://prove2.me/theorems/1738d729-e35b-453c-a0af-761ecfc36977
-- title:
--   IV A 1: all states invariant under collective polarization noise
-- statement:
--   Let $\mathcal H$ be any nonzero finite-dimensional Hilbert space, $n\ge1$, and $\rho$ any trace-one positive semidefinite operator on $(\mathbb C^2\otimes\mathcal H)^{\otimes n}$. Then
--   $$\bigl[\forall V\in U(2),\ (V\otimes I)^{\otimes n}\rho((V\otimes I)^{\otimes n})^*=\rho\bigr]
--   \iff \rho\in\operatorname{Alg}(P(S_n),(I_2\otimes\operatorname{End}(\mathcal H))^{\otimes n}).$$
--   This characterizes all states unaffected by collective polarization noise, independently of a distribution over noise unitaries.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 12, IV A 1: all states invariant under collective polarization noise

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

/-- PDF pp.11-12, IV A 1: exact characterization of every invariant density
operator under collective polarization noise, with an arbitrary finite degree
of freedom H left unchanged. -/
theorem polarization_noiseless_states {H : Type*} [Fintype H] [DecidableEq H]
    [Nonempty H] (n : ℕ) (hn : 0 < n) (rho : Mat (Fin n → Fin 2 × H))
    (hrho : IsDensityMatrix rho) :
    (∀ V : Mat (Fin 2), Vᴴ * V = 1 → V * Vᴴ = 1 →
      let U := piKron n (Matrix.kronecker V (1 : Mat H))
      U * rho * Uᴴ = rho) ↔
    rho ∈ alg (permutations (Fin 2 × H) n ∪
      tensorAlg n {X : Mat (Fin 2 × H) | ∃ Y : Mat H,
        X = Matrix.kronecker (1 : Mat (Fin 2)) Y}) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
