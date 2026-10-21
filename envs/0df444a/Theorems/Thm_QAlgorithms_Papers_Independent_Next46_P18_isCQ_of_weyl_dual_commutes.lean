-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_isCQ_of_weyl_dual_commutes
-- name    : QAlgorithms.Papers.Independent.Next46.P18.isCQ_of_weyl_dual_commutes
-- status  : Open
-- author  : @Imine
-- created : 2026-10-21T00:59:35.662536+00:00
-- url     : https://prove2.me/theorems/29e982ac-6018-4981-b69a-01ed062eeded
-- title:
--   Normality and Weyl density extend commutation from Weyl generators
-- statement:
--   Let $H_I$ and $H_J$ be the separable Hilbert spaces of two finite-mode bosonic systems, and let $W_B$ be a regular irreducible Weyl representation on $H_J$ with $t$ modes. Let $\Phi$ be a channel whose dual $\Phi^*:B(H_J)\to B(H_I)$ is related to the predual by the trace pairing.
--
--   Suppose that for all phase-space vectors $z,w$,
--   $$
--   \Phi^*(W_B(z))\,\Phi^*(W_B(w))=\Phi^*(W_B(w))\,\Phi^*(W_B(z)).
--   $$
--   Then the images of *all* pairs of bounded operators commute:
--   $$
--   \Phi^*(B)\,\Phi^*(C)=\Phi^*(C)\,\Phi^*(B)
--   \qquad (B,C\in B(H_J)).
--   $$
--
--   The point is that the hypothesis only tests the Weyl generators, while the conclusion is the full classical-quantum condition. Two standard facts bridge the gap. First, the trace-class pairing makes $\Phi^*$ the adjoint of a bounded map on trace class, hence normal (weakly continuous). Second, the Weyl algebra of a regular irreducible representation is weakly dense in $B(H_J)$ (von Neumann's density theorem). The weak limit of a commuting family lies in a commutative algebra, so normality transfers commutation from the Weyl generators to every bounded operator. The zero-mode case is included: irreducibility then forces the output space to be one-dimensional, where commutation is automatic.
--
--   This lemma isolates the operator-algebraic step in the proof of the Gaussian c-q criterion $K^{\mathsf T}\Delta_A K=0$; the Gaussian computation itself only needs to check commutation on the Weyl images.
-- source:
--   Auxiliary operator-algebra lemma for Holevo, Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 5, section 3, criterion (14). The paper uses the standard weak density of irreducible Weyl systems and normality of the dual; the lemma states that step separately.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

namespace QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- If the dual of a channel sends the Weyl operators of an irreducible
finite-mode representation to a commuting family, then the whole dual range
is commutative. This is the operator-algebraic extension step behind the
Gaussian c-q criterion: the dual is normal by its trace-class pairing, and
the Weyl algebra of an irreducible regular representation is weakly dense
in the bounded operators. -/
theorem isCQ_of_weyl_dual_commutes {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] {t : ℕ}
    (WB : ScaledWeylRepresentation J t 1) (Phi : DualChannel I J)
    (h : ∀ z w : InterleavedPhase t,
      (Phi.dual (WB.operator z)).comp (Phi.dual (WB.operator w)) =
      (Phi.dual (WB.operator w)).comp (Phi.dual (WB.operator z))) :
    IsCQ Phi := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end
