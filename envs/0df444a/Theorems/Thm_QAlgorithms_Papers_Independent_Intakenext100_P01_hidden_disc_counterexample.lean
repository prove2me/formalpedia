-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_hidden_disc_counterexample
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.hidden_disc_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:18:36.56914+00:00
-- url     : https://prove2.me/theorems/e1e859b9-17ff-425e-84c2-599c5472a80a
-- title:
--   A hidden disc gives an EB channel outside essentially CQ
-- statement:
--   Let $T_2:M_2(\mathbb C)\to M_2(\mathbb C)$ be a unital quantum channel whose Bloch image is a filled disc $D$ of radius $1/2$ centered at the maximally mixed state. Let $d\ge1$, let $(e_i)_{i=1}^d$ be an orthonormal basis of $\mathbb C^d$, and let $(\sigma_i)_{i=1}^d$ be full-rank qubit density matrices forming exactly the distinct vertices of their convex hull, with $D\subseteq\operatorname{conv}\{\sigma_i\}$. Define $T_1(A)=\sum_i\langle e_i,Ae_i\rangle\sigma_i$ and $T(A)=T_1(A_{11})+T_2(A_{22})$ on $M_{d+2}(\mathbb C)$. Then
--   $$\operatorname{Im}T\text{ is polytopic},\qquad T\text{ is entanglement breaking},\qquad T\text{ is not essentially classical-quantum}.$$
--
--   This separates essentially classical-quantum channels from entanglement-breaking channels with polytopic images.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 13, Proposition 7.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Proposition 7.3, PDF pp.13–14: a hidden unital disc of radius one half yields a
polytopic EB channel that is not essentially CQ. Mixed qubit vertices have full rank.
Source correction: Appendix (22) prints I/2 + sum w_j sigma_j; changed to
(I + sum w_j sigma_j)/2 to match its stated unit Bloch ball and this radius 1/2. -/
theorem hidden_disc_counterexample {d : ℕ} (hd : 0 < d)
    (T2 : Superop (Fin 2) (Fin 2)) (hT2 : IsChannel T2) (hUnital : T2 1 = 1)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hL : Module.finrank ℝ L = 2)
    (hDisc : channelImage T2 = blochDisc (1 / 2) L)
    (e : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (s : Fin d → Mat 2)
    (hs : ∀ i, IsDensityMatrix (s i) ∧ (s i).PosDef)
    (hVertices : HasVertices (convexHull ℝ (Set.range s)) s)
    (hContains : blochDisc (1 / 2) L ⊆ convexHull ℝ (Set.range s)) :
    IsPolytopic (channelImage (diagonalBlockSum (cqMap e s) T2)) ∧
      IsEB (diagonalBlockSum (cqMap e s) T2) ∧
      ¬ IsEssentialCQ (diagonalBlockSum (cqMap e s) T2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
