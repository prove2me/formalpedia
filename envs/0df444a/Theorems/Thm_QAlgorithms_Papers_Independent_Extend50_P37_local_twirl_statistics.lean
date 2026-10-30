-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_local_twirl_statistics
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.local_twirl_statistics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:26:42.125631+00:00
-- url     : https://prove2.me/theorems/f0ec1510-11b8-4278-a320-da72bef7bd16
-- title:
--   IV B 1: a locally symmetric POVM ignores local twirling
-- statement:
--   Let $d,n\ge1$, let $H\le U(d)$ carry an actual normalized invariant Haar law, and let $M$ be a normalized countably additive POVM on an arbitrary measurable outcome space with local $H$ symmetry. Its effects are fixed by $T_H^{\otimes n}$, and for every density matrix $\rho$ and measurable event $B$,
--   $$\operatorname{tr}(M(B)\rho)=\operatorname{tr}(M(B)T_H^{\otimes n}(\rho)).$$
--   The twirled state lies in $\operatorname{Alg}(H')^{\otimes n}$. Moreover, on ordered left/right registers, every POVM taking values in $(\operatorname{End}(\mathcal H_L)\otimes I_R)^{\otimes n}$ equals a left POVM tensored with the right identity. Its statistics are those of that POVM on the actual reduced state $\operatorname{Tr}_{R^{\otimes n}}\rho$. This bounds the needed quantum register without requiring commutativity.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 13, IV B 1: a locally symmetric POVM ignores local twirling

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

/-- PDF pp.13-14, IV B 1: local twirling fixes effects, leaves all event
probabilities unchanged, and sends states into the local centralizer algebra. -/
theorem local_twirl_statistics [Nonempty I] {O : Type*} [MeasurableSpace O]
    {L R : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (n : ℕ) (hn : 0 < n) (H : Set (Mat I)) (mu : Measure (Mat I))
    (hmu : SubgroupHaarProbability H mu) (M : Measurements.OperatorPOVM (Fin n → I) O)
    (hM : InAlgebra M.operator (Set.centralizer (localSet n H))) :
    (∀ B, MeasurableSet B → piSuperop (fun _ : Fin n => subgroupConjugationAverage mu) (M.operator B) = M.operator B) ∧
    (∀ rho, IsDensityMatrix rho →
      piSuperop (fun _ : Fin n => subgroupConjugationAverage mu) rho ∈ tensorAlg n (alg (unitaryCentralizer H)) ∧
      ∀ B, MeasurableSet B → effectProb (M.operator B) rho =
        effectProb (M.operator B) (piSuperop (fun _ : Fin n => subgroupConjugationAverage mu) rho)) ∧
    (∀ F : Measurements.OperatorPOVM (Fin n → L × R) O,
      InAlgebra F.operator (tensorAlg n
        {X : Mat (L × R) | ∃ Y : Mat L, X = Matrix.kronecker Y (1 : Mat R)}) →
      ∃ N : Measurements.OperatorPOVM (Fin n → L) O,
        (∀ B, MeasurableSet B → F.operator B = liftLeftRegister (R := R) (N.operator B)) ∧
        ∀ rho, IsDensityMatrix rho → ∀ B, MeasurableSet B →
          effectProb (F.operator B) rho = effectProb (N.operator B) (traceRightRegister rho)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
