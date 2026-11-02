-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P97_rays_not_entropic
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P97.rays_not_entropic
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:43:08.847213+00:00
-- url     : https://prove2.me/theorems/965c6ce8-d7d4-4434-a5c3-fac6dbe36b06
-- title:
--   Corollary 5: nonzero rays I and II are not entropic
-- statement:
--   Let $\rho_{ABCD}$ be a positive semidefinite complex density matrix of trace one on four finite-dimensional tensor factors $A,B,C,D$, each of positive dimension (dimension one is allowed). Every $S(X)$ is the base-two von Neumann entropy of the actual $X$ marginal of this same state, with $0\log_2 0=0$. For disjoint groups write $S(X\mid Y)=S(XY)-S(Y)$, $I(X;Y)=S(X)+S(Y)-S(XY)$, and $I(X;Z\mid Y)=S(XY)+S(YZ)-S(XYZ)-S(Y)$. In the coordinate order $(A,B,C,D,AB,AC,AD,BC,BD,CD,ABC,ABD,ACD,BCD,ABCD)$, define the two formal entropy vectors by
--
--   $$
--   v_1=(3,3,2,2,4,3,3,3,3,4,4,4,3,3,2),\qquad
--   v_2=(3,3,3,3,4,4,4,4,4,6,5,5,5,5,2).
--   $$
--
--   Set the empty coordinate to zero. Mutual information and conditional mutual information of these formal vectors mean the corresponding linear combinations of their coordinates. For every $t>0$,
--
--   $$
--   (S(X))_{X\ne\varnothing}\notin\{t v_1,t v_2\}.
--   $$
--
--   Both positive rays satisfy all basic inequalities and the three constraints $I(A;C\mid B)=I(B;C\mid A)=I(A;B\mid D)=0$, but have $I(C;D)<I(C;AB)$, so they lie in the slice removed by the new inequality within that constrained face. This excludes exact finite-dimensional realization, with no assertion about approximating these rays by entropic vectors.
-- source:
--   A new inequality for the von Neumann entropy, arXiv:quant-ph/0406162v1, PDF p. 6, Corollary 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P97

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P97

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "A" => ({0} : Finset (Fin 4))

local notation "B" => ({1} : Finset (Fin 4))

local notation "C" => ({2} : Finset (Fin 4))

local notation "D" => ({3} : Finset (Fin 4))

/-- PDF p.6, Corollary 5: neither nonzero ray is exactly entropic in finite
systems. The zero endpoint is excluded, and no assertion about limit points is made. -/
theorem rays_not_entropic (q : FourPartyState) (t : ℝ) (ht : 0 < t) :
    (¬ ((∀ s, fourPartyEntropyBits q s = t * rayOne s) ∨ (∀ s, fourPartyEntropyBits q s = t * rayTwo s))) ∧
    (∀ h ∈ ({rayOne, rayTwo} : Set (Finset (Fin 4) → ℝ)),
      BasicInequalities (fun s => t * h s) ∧ Constraints (fun s => t * h s) ∧
      mutualValue (fun s => t * h s) C D < mutualValue (fun s => t * h s) C (A ∪ B)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P97

end
