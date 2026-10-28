-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_pureEnsemblesSuffice
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.pureEnsemblesSuffice
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:15:42.537828+00:00
-- url     : https://prove2.me/theorems/21de5956-d158-49b4-ba56-b3600a51ebbe
-- title:
--   §6.1, unnumbered: pure state ensembles are sufficient
-- statement:
--   Let $\mathcal N:A'\to B$ be a completely positive trace-preserving map between nonzero finite-dimensional quantum registers. All entropies are in bits, with $0\log 0=0$. Every ensemble is finite, its weights are nonnegative and sum to one, and every component is normalized, including components of weight zero.
--
--   Fix any nonzero finite reference $A$ and mixed bipartite input ensemble $\{p_x,\rho_x^{AA'}\}$, and let $\rho_x^{AB}=(\mathrm{id}_A\otimes\mathcal N)(\rho_x^{AA'})$. There exist a finite nonempty refinement alphabet $Y$, conditional probabilities $q(y\mid x)$, and normalized pure states $\psi_{xy}^{AA'}$, such that each conditional probability distribution sums to one and
--
--   $$\rho_x^{AA'}=\sum_y q(y\mid x)\psi_{xy}^{AA'},\qquad \rho_x^{AB}=\sum_y q(y\mid x)(\mathrm{id}_A\otimes\mathcal N)(\psi_{xy}).$$
--
--   Thus forgetting $Y$ recovers the original cq output. If $\theta^{XYAB}$ records $(x,y)$ with probability $p_xq(y\mid x)$, then simultaneously
--
--   $$I(X;B)_\rho\le I(XY;B)_\theta,\qquad I(AX;B)_\rho\le I(AXY;B)_\theta,\qquad I(A\rangle BX)_\rho\le I(A\rangle BXY)_\theta.$$
--
--   Conditional coherent information means the average of $H(B)-H(AB)$, rather than mutual information. The refinement is constructed for every original ensemble, including its zero-weight labels. This reduction justifies restricting the dynamic region to pure ensembles.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 10, §6.1, unnumbered: pure state ensembles are sufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 6.1, PDF pp.10--11 (16)--(20): construct a pure refinement of EACH
mixed ensemble, recover each original conditional output by forgetting Y, and improve
all three information quantities simultaneously. Zero-weight x are included. -/
theorem pureEnsemblesSuffice
    {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    [Nonempty A] [Nonempty B] [Nonempty R]
    (N : Superop A B) (hN : IsChannel N) (e : Ensemble (R × A)) :
    ∃ k : ℕ, 0 < k ∧ ∃ q : Fin e.size → Fin k → ℝ,
      ∃ psi : Fin e.size → Fin k → EuclideanSpace ℂ (R × A),
      (∀ x y, 0 ≤ q x y) ∧ (∀ x, ∑ y, q x y = 1) ∧
      (∀ x y, ‖psi x y‖ = 1) ∧
      (∀ x, e.state x = ∑ y, q x y • pureDensity (psi x y)) ∧
      (∀ x, idTensorSuperop N (e.state x) =
        ∑ y, q x y • idTensorSuperop N (pureDensity (psi x y))) ∧
      (let rho := fun x => idTensorSuperop N (e.state x)
       let theta := fun xy : Fin e.size × Fin k => idTensorSuperop N (pureDensity (psi xy.1 xy.2))
       let p := fun xy : Fin e.size × Fin k => e.prob xy.1 * q xy.1 xy.2
       cqHolevoBits e.prob rho ≤ cqHolevoBits p theta ∧
       jointMutual e.prob rho ≤ jointMutual p theta ∧
       conditionalCoherent e.prob rho ≤ conditionalCoherent p theta) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
