-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P37_virtualEntanglement
-- name    : QAlgorithms.Papers.Independent.Advance50.P37.virtualEntanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:39:58.22436+00:00
-- url     : https://prove2.me/theorems/0519a617-3380-4d0c-aebe-4f7cfe884db6
-- title:
--   The full Fock resource realizes the spherical coherent-state ensemble
-- statement:
--   Fix $\alpha>0$. For each $k\ge0$ put $d_k=\binom{k+3}{3}$ and
--
--   $$
--   |\psi_k^4\rangle=d_k^{-1/2}\sum_{n_1+\cdots+n_4=k}|n_1,n_2,n_3,n_4\rangle_A|n_1,n_2,n_3,n_4\rangle_B,
--   \qquad |\Psi_\alpha\rangle=e^{-2\alpha^2}\sum_{k=0}^\infty\frac{(2\alpha)^k}{\sqrt{k!}}|\psi_k^4\rangle.
--   $$
--
--   The series converges in the completed eight-mode Fock space to a unit vector with precisely these coefficients. Its rank-one density and Bob's partial trace are normalized positive trace-class states; the defining partial-trace coefficient sums converge. Let $\mu_\alpha$ be normalized surface measure on $S^7(2\alpha)\subset\mathbb R^8$, and let $C(x)$ be the rank-one density of the four coherent states obtained by pairing successive coordinates of $x$. Then
--
--   $$
--   \operatorname{Tr}_A|\Psi_\alpha\rangle\langle\Psi_\alpha|=\int C(x)\,d\mu_\alpha(x).
--   $$
--
--   There exists a normalized, positive, weakly countably additive Borel POVM $M$ on Alice's four modes such that for every Borel set $S$, Bob's unnormalized state after Alice's effect $M(S)$ is $\int_S C(x)\,d\mu_\alpha(x)$ and its trace is $\mu_\alpha(S)$. All coefficient integrals and event-trace series converge. The coherent vectors have unit norm and their densities are normalized almost everywhere. Thus $C(x)$ is a version of the conditional Bob state almost everywhere, and Alice's outcome distribution is exactly $\mu_\alpha$.
--
--   This is the prepare-and-measure equivalence claimed for the specific constructed resource; no photon cutoff or assumed steering measurement is used.
-- source:
--   Long distance quantum key distribution with continuous variables, arXiv:1005.0328v3, PDF p. 6, Section 3, Eq. (3): normalized virtual entangled state and prepare-and-measure equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P37

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P37

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Gap48.P26 (totalPhotons)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsBarycenter IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov standardFormCovariance vacuumKernel productWeyl weylArgument)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation partialRight)

open QAlgorithms.Papers.Independent.Support50.P14 (CompleteMoments GaussianAt)

open QAlgorithms.Papers.Independent.Renew46.P39 (squeezedVacuum)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProductCoefficient NormalizedCoherent)

/-- PDF p.6, Eq.(3): the constructed resource converges, is normalized, has
Bob marginal equal to the spherical mixture, and admits Alice's steering POVM
with the correct outcome law. Conditional coherent densities are interpreted
almost everywhere via the displayed integral disintegration on measurable sets.
Existence, normalization and the steering identities are conclusions. -/
theorem virtualEntanglement (alpha : ℝ) (halpha : 0 < alpha) :
    (∃ psi : Hilbert ((Fin 4 ⊕ Fin 4) → ℕ),
      HasSum (virtualSummand alpha) psi ∧ ‖psi‖ = 1 ∧
      (∀ n, psi n = virtualCoefficient alpha n)) ∧
    IsDensity (virtualDensity alpha) ∧
    (∀ b d, Summable (fun a : FockIndex 4 =>
      virtualDensity alpha (Sum.elim a b) (Sum.elim a d))) ∧
    IsDensity (sphericalBobMarginal alpha) ∧
    IsBarycenter (sphericalModulation alpha) sphereCoherentDensity
      (sphericalBobMarginal alpha) ∧
    (∀ᵐ x ∂sphericalModulation alpha,
      NormalizedCoherent (modulationAmplitudes x) ∧ IsDensity (sphereCoherentDensity x)) ∧
    ∃ M : SphericalSteeringPOVM, ∀ S : Set ModulationSpace, MeasurableSet S →
      (∀ b d, Integrable (fun x => sphereCoherentDensity x b d)
        ((sphericalModulation alpha).restrict S) ∧
        steeredBobKernel alpha M S b d =
          ∫ x in S, sphereCoherentDensity x b d ∂sphericalModulation alpha) ∧
      Summable (fun b => (steeredBobKernel alpha M S b b).re) ∧
      steeringEventProbability alpha M S = (sphericalModulation alpha S).toReal := by sorry

end QAlgorithms.Papers.Independent.Advance50.P37

end
