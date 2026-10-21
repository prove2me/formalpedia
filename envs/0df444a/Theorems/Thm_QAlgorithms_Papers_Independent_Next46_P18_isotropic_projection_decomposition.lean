-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_isotropic_projection_decomposition
-- name    : QAlgorithms.Papers.Independent.Next46.P18.isotropic_projection_decomposition
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-20T17:06:46.401631+00:00
-- url     : https://prove2.me/theorems/dcef03e7-2ecc-459f-b6e4-90af7839b998
-- title:
--   §3 Lemma, linear-algebra step: isotropic projection decomposition
-- statement:
--   Let $s,t\ge 0$ be mode counts, and let $\Omega_s$ be the canonical symplectic matrix on $\mathbb{R}^{2s}$ written in interleaved real coordinates $(q_1,p_1,\dots,q_s,p_s)$:
--   $$
--   (\Omega_s)_{(j,0),(j,1)}=1,\qquad
--   (\Omega_s)_{(j,1),(j,0)}=-1
--   $$
--   for $0\le j<s$, with all remaining entries zero. Let $K\colon\mathbb{R}^{2t}\to\mathbb{R}^{2s}$ be a real matrix whose range is isotropic with respect to $\Omega_s$, that is,
--   $$
--   K^{\mathsf T}\Omega_sK=0.
--   $$
--
--   Then there exist real $2s\times 2s$ matrices $P,Q,R$ with the following properties.
--
--   1. **Projections.** $P,Q,R$ are symmetric and idempotent:
--   $$
--   P^{\mathsf T}=P,\quad Q^{\mathsf T}=Q,\quad R^{\mathsf T}=R,\qquad
--   P^2=P,\quad Q^2=Q,\quad R^2=R.
--   $$
--
--   2. **Orthogonal decomposition.** They are mutually orthogonal and sum to the identity:
--   $$
--   PQ=PR=QR=0,\qquad P+Q+R=\mathbf 1.
--   $$
--
--   3. **Symplectic symmetry.** The second projection is the symplectic conjugate of the first:
--   $$
--   Q=-\Omega_sP\Omega_s.
--   $$
--
--   4. **Action on the range of $K$.** The coupling is carried entirely by the first summand:
--   $$
--   K^{\mathsf T}PK=K^{\mathsf T}K,\qquad
--   K^{\mathsf T}QK=0,\qquad
--   K^{\mathsf T}RK=0.
--   $$
--
--   Geometrically, $P,Q,R$ are the orthogonal projections onto three mutually orthogonal subspaces spanning $\mathbb{R}^{2s}$: the closure of the range of $K$, its image $\Omega_s(\operatorname{Ran}K)$ under the symplectic matrix, and their common orthogonal complement. Isotropy of the range is exactly what makes the first two summands orthogonal.
--
--   This decomposition is the finite-dimensional linear-algebra input to the squeezing construction for Gaussian classical-quantum channels with isotropic coupling. It separates the directions seen by $K$ from the two symplectically conjugate directions that carry the squeezing parameter. The statement includes the degenerate cases $s=0$ and $t=0$; when $K=0$ one may take $P=0$, $Q=0$, $R=\mathbf 1$.
--
--   **Formalization Note** The symplectic matrix is the platform definition `physicalCommutationMatrix s 1`; `QuadratureIndex s` indexes the $2s$ interleaved phase-space coordinates. All matrices are real, and `0` on the right-hand side of the isotropy hypothesis is the zero matrix of size $2t\times 2t$.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF pp. 7-8, §3, unnumbered Lemma (squeezing construction). This child isolates the finite-dimensional orthogonal projection decomposition used in the proof of that lemma.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18

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

/-- For an isotropic range of `K`, the orthogonal projections onto `Ran K`, its
symplectic image under the commutation matrix, and the common orthogonal
complement satisfy the algebra needed for the squeezing construction. -/
theorem isotropic_projection_decomposition {s t : ℕ}
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (hK : K.transpose * (physicalCommutationMatrix s 1) * K = 0) :
    ∃ P Q R : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
      P.IsSymm ∧ Q.IsSymm ∧ R.IsSymm ∧
      P * P = P ∧ Q * Q = Q ∧ R * R = R ∧
      P * Q = 0 ∧ P * R = 0 ∧ Q * R = 0 ∧
      P + Q + R = 1 ∧
      Q = -(physicalCommutationMatrix s 1) * P * (physicalCommutationMatrix s 1) ∧
      K.transpose * P * K = K.transpose * K ∧
      K.transpose * Q * K = 0 ∧
      K.transpose * R * K = 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end
