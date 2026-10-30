-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_local_commutant_permutation_invariant
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.local_commutant_permutation_invariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:22:42.210991+00:00
-- url     : https://prove2.me/theorems/5bf73280-1a18-45c6-a997-1e3a62aaf14b
-- title:
--   Corollary 6: permutation-invariant local commutant
-- statement:
--   For any unitary subgroup $H\le U(d)$ and $d,n\ge1$, with $H'$ its unitary centralizer,
--   $$\operatorname{Comm}(H^{\times n})\cap\operatorname{Comm}(P(S_n))=\operatorname{Alg}(Q(H')).$$
--   The original group need not be gauge; this describes the permutation-invariant local commutant.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 8, Corollary 6: permutation-invariant local commutant

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

/-- PDF p.8, Corollary 6: H may be any unitary subgroup. -/
theorem local_commutant_permutation_invariant [Nonempty I] (n : ℕ) (hn : 0 < n)
    (H : Set (Mat I)) (hH : UnitarySubgroup H) :
    Set.centralizer (localSet n H) ∩ Set.centralizer (permutations I n) = alg (collectiveImage n (unitaryCentralizer H)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
