-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_sector_duality
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.sector_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:23:39.522986+00:00
-- url     : https://prove2.me/theorems/a7ba5a86-8adb-44d9-aaee-42898bbc48df
-- title:
--   Theorem 7: duality within symmetric and antisymmetric subspaces
-- statement:
--   Let $G,H\le U(d)$ be mutual unitary centralizers, $d,n\ge1$, and choose either the symmetric or antisymmetric projector $\Pi_\pm$. Inside $\operatorname{End}(\operatorname{ran}\Pi_\pm)$,
--   $$\operatorname{Comm}(Q(G)|_\pm)=\operatorname{Alg}(Q(H)|_\pm),\qquad
--   \operatorname{Comm}(Q(H)|_\pm)=\operatorname{Alg}(Q(G)|_\pm).$$
--   These are the sector dual reductive pair identities. The antisymmetric sector may have dimension zero; no condition $n\le d$ is imposed.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 9, Theorem 7: duality within symmetric and antisymmetric subspaces

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

/-- PDF pp.9-10, Theorem 7: commutants are taken inside the chosen sector,
including the zero antisymmetric sector when n exceeds the dimension.
The missing 1/n! in proof (3.9) is not used as an assumption. -/
theorem sector_duality [Nonempty I] (n : ℕ) (hn : 0 < n) (s : Bool)
    (G H : Set (Mat I)) (hG : UnitarySubgroup G) (hH : UnitarySubgroup H)
    (hGH : unitaryCentralizer G = H) (hHG : unitaryCentralizer H = G) :
    cornerComm (permutationSector I n s) (collectiveImage n G) = cornerAlg (permutationSector I n s) (collectiveImage n H) ∧
      cornerComm (permutationSector I n s) (collectiveImage n H) = cornerAlg (permutationSector I n s) (collectiveImage n G) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
