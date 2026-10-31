-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_hidden_ball_counterexample
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.hidden_ball_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:19:29.749192+00:00
-- url     : https://prove2.me/theorems/853a2f38-b2c0-43f3-9302-ebe0d4cc857a
-- title:
--   A hidden depolarizing ball gives a second separation
-- statement:
--   Let $\Delta_{1/3}:M_2(\mathbb C)\to M_2(\mathbb C)$ be the depolarizing channel, with linear extension $\Delta_r(A)=rA+(1-r)\operatorname{Tr}(A)I_2/2$. Its state image is the filled Bloch ball $S$ of radius $1/3$. Let $d\ge1$, choose an orthonormal basis $(e_i)$ of $\mathbb C^d$, and full-rank qubit density matrices $(\sigma_i)$ forming exactly the distinct vertices of a polytope containing $S$. With $T_1(A)=\sum_i\langle e_i,Ae_i\rangle\sigma_i$, define $T(A)=T_1(A_{11})+\Delta_{1/3}(A_{22})$ on $M_{d+2}(\mathbb C)$. Then
--   $$\operatorname{Im}T\text{ is polytopic},\qquad T\text{ is entanglement breaking},\qquad T\text{ is not essentially classical-quantum}.$$
--
--   This is the three-dimensional version of the channel-class separation.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 14, Proposition 7.4

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

/-- Proposition 7.4, PDF p.14: qubitDepolarizing parameter one third, with a containing
polytope of full-rank qubit states, gives all three asserted properties. “Sphere” is a filled ball.
Source correction: Appendix (22) prints I/2 + sum w_j sigma_j; changed to
(I + sum w_j sigma_j)/2 to match its stated unit Bloch ball and this radius 1/3. -/
theorem hidden_ball_counterexample {d : ℕ} (hd : 0 < d)
    (e : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (s : Fin d → Mat 2)
    (hs : ∀ i, IsDensityMatrix (s i) ∧ (s i).PosDef)
    (hVertices : HasVertices (convexHull ℝ (Set.range s)) s)
    (hContains : blochBall (1 / 3) ⊆ convexHull ℝ (Set.range s)) :
    IsPolytopic (channelImage (diagonalBlockSum (cqMap e s) (qubitDepolarizing (1 / 3)))) ∧
      IsEB (diagonalBlockSum (cqMap e s) (qubitDepolarizing (1 / 3))) ∧
      ¬ IsEssentialCQ (diagonalBlockSum (cqMap e s) (qubitDepolarizing (1 / 3))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
