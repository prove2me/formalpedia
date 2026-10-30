-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_ns_identities
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.ns_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:42:35.792535+00:00
-- url     : https://prove2.me/theorems/c305f3f0-e5c9-4182-9d86-0081a4d19f77
-- title:
--   Ns Identities: ns identities
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Choose spectral decompositions $\rho=\sum_a r_a|\phi_a\rangle\langle\phi_a|$ and $\sigma=\sum_b s_b|\psi_b\rangle\langle\psi_b|$ in orthonormal eigenbases. Define
--   $$
--   P(a,b)=r_a|\langle\phi_a|\psi_b\rangle|^2,\qquad Q(a,b)=s_b|\langle\phi_a|\psi_b\rangle|^2.
--   $$
--   These are probability mass functions and satisfy
--   $$
--   D(\rho\|\sigma)=D(P\|Q),\qquad
--   \ker\sigma\subseteq\ker\rho\iff(\forall a,b:\ Q(a,b)=0\Rightarrow P(a,b)=0).
--   $$
--   On this support-dominated domain, also $V(\rho\|\sigma)=V(P\|Q)$. For two pairs of states, use the tensor products of the chosen eigenbases. Their resulting NS laws are exactly $P_1\otimes P_2$ and $Q_1\otimes Q_2$, under the canonical regrouping of the two label pairs.
--
--   This summarizes (B1)–(B3) while retaining basis choices in degenerate eigenspaces and the source domain of finite variance.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 25, Ns Identities

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Appendix B, PDF pp.25–26, (B1)–(B3): normalized NS laws, entropy and variance
identities, support equivalence and literal product laws in the PRODUCT eigenbasis.
Variance is stated on its source domain, sigma dominating rho. -/
theorem ns_identities {I : Type} {J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (r s : NSSpectralData I) (hr : IsSpectral rho r) (hs : IsSpectral sigma s) :
    ((∀ a, 0 ≤ nsP r s a ∧ 0 ≤ nsQ r s a) ∧
      (∑ a, nsP r s a) = 1 ∧ (∑ a, nsQ r s a) = 1) ∧
    entropy rho sigma = nsClassicalD (nsP r s) (nsQ r s) ∧
    (Dominates sigma rho → pairInformationVariance rho sigma = classicalV (nsP r s) (nsQ r s)) ∧
    (Dominates sigma rho ↔ ∀ a, nsQ r s a = 0 → nsP r s a = 0) ∧
    (∀ rho2 sigma2 : Mat J, QAlgorithms.IsDensityMatrix rho2 → QAlgorithms.IsDensityMatrix sigma2 →
      ∀ r2 s2 : NSSpectralData J, IsSpectral rho2 r2 → IsSpectral sigma2 s2 →
      IsSpectral (Matrix.kronecker rho rho2) (productSpectral r r2) ∧
      IsSpectral (Matrix.kronecker sigma sigma2) (productSpectral s s2) ∧
      ∀ (a : I × I) (b : J × J),
        nsP (productSpectral r r2) (productSpectral s s2) ((a.1,b.1),(a.2,b.2)) =
          nsP r s a * nsP r2 s2 b ∧
        nsQ (productSpectral r r2) (productSpectral s s2) ((a.1,b.1),(a.2,b.2)) =
          nsQ r s a * nsQ r2 s2 b) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
