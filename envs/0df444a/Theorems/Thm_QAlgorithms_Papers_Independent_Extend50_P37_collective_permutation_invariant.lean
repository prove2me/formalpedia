-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_collective_permutation_invariant
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.collective_permutation_invariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:21:37.811998+00:00
-- url     : https://prove2.me/theorems/89574b27-66e0-44c9-b6ee-d24a49c8c1dc
-- title:
--   Lemma 5: collective algebra equals permutation-invariant local algebra
-- statement:
--   Let $G\le U(d)$ be a gauge group and $d,n\ge1$. Then
--   $$\operatorname{Alg}(Q(G))=\operatorname{Alg}(G^{\times n})\cap\operatorname{Comm}(P(S_n))
--   =\operatorname{Alg}(G)^{\otimes n}\cap\operatorname{Comm}(P(S_n)).$$
--   Thus its collective algebra is exactly the permutation-invariant part of its local algebra. The gauge hypothesis is essential.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 8, Lemma 5: collective algebra equals permutation-invariant local algebra

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

/-- PDF p.8, Lemma 5; Appendix A pp.33-34. -/
theorem collective_permutation_invariant [Nonempty I] (n : ℕ) (hn : 0 < n)
    (G : Set (Mat I)) (hG : IsGauge G) :
    alg (collectiveImage n G) = alg (localSet n G) ∩ Set.centralizer (permutations I n) ∧
      alg (collectiveImage n G) = tensorAlg n (alg G) ∩ Set.centralizer (permutations I n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
