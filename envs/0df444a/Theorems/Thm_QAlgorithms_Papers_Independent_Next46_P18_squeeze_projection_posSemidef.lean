-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_squeeze_projection_posSemidef
-- name    : QAlgorithms.Papers.Independent.Next46.P18.squeeze_projection_posSemidef
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-20T17:06:37.618733+00:00
-- url     : https://prove2.me/theorems/44d6df7a-fa9c-41bb-9a3e-7e3a6aef978b
-- title:
--   §3 Lemma, positivity step: squeezed block covariance is positive semidefinite
-- statement:
--   Let $s\ge 0$, let $\Omega_s$ be the canonical symplectic matrix on $\mathbb{R}^{2s}$ in interleaved real coordinates, with
--   $$
--   (\Omega_s)_{(j,0),(j,1)}=1,\qquad
--   (\Omega_s)_{(j,1),(j,0)}=-1,
--   $$
--   and all other entries zero. Let $P,Q,R$ be real symmetric $2s\times 2s$ matrices satisfying the projection identities
--   $$
--   P^2=P,\qquad Q^2=Q,\qquad R^2=R,\qquad
--   PQ=PR=QR=0,\qquad P+Q+R=\mathbf 1,
--   $$
--   and the symplectic relation
--   $$
--   Q=-\Omega_sP\Omega_s.
--   $$
--
--   Then for every positive integer $n\ge 1$, the complex $2s\times 2s$ matrix
--   $$
--   M_n=\left(\frac{1}{n}P+nQ+R\right)+i\,\Omega_s
--   $$
--   is positive semidefinite.
--
--   The three summands are the block-diagonal weights attached to the three mutually orthogonal projections, with the first squeezed down by $1/n$ and the second squeezed up by $n$. The imaginary part $i\Omega_s$ is the fixed vacuum noise term; its presence forces the two symplectically conjugate blocks to be treated together, and the weights $1/n$ and $n$ are precisely the pair for which the resulting block matrix is positive semidefinite with a kernel direction. Thus $M_n$ is the complex covariance matrix of a physical (pure, in the two active blocks) Gaussian state, while the third block is unconstrained by the symplectic form.
--
--   This is the second half of the squeezing construction for Gaussian classical-quantum channels: it certifies that the block-diagonal matrices used to drive the compressed covariance of an isotropic coupling to zero are themselves legitimate quantum covariances. The case $n=1$ reduces to the vacuum covariance $P+Q+R+i\Omega_s=\mathbf 1+i\Omega_s$.
--
--   **Formalization Note** Positive semidefiniteness is `Matrix.PosSemidef` for complex matrices; the real matrix is embedded via entrywise coercion, and $\Omega_s$ is the platform definition `interleavedSymplecticForm s`.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF pp. 7-8, §3, unnumbered Lemma (squeezing construction). This child isolates the positive-semidefiniteness check for the block-diagonal squeezed covariance.

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

/-- The paper's block-diagonal squeezed covariance is a physical covariance.
`P`, `Q = -Delta P Delta` and `R` are the three mutually orthogonal projections
of the projection decomposition; `n` is the squeezing parameter. -/
theorem squeeze_projection_posSemidef {s : ℕ}
    (P Q R : Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ)
    (hPsym : P.IsSymm) (hQsym : Q.IsSymm) (hRsym : R.IsSymm)
    (hPid : P * P = P) (hQid : Q * Q = Q) (hRid : R * R = R)
    (hPQ : P * Q = 0) (hPR : P * R = 0) (hQR : Q * R = 0)
    (hsum : P + Q + R = 1)
    (hQ : Q = -(QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s) * P *
      (QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s))
    (n : ℕ) (hn : 0 < n) :
    (((1 / (n : ℝ)) • P + (n : ℝ) • Q + R).map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (QAlgorithms.Papers.Independent.Frontier30.P08.interleavedSymplecticForm s).map
        (fun x : ℝ => (x : ℂ))).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end
