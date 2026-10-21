-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_fixed_known_squeezing_cloner
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.fixed_known_squeezing_cloner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:25:46.868989+00:00
-- url     : https://prove2.me/theorems/f85bd263-2b07-4816-be74-5dfd409be4db
-- title:
--   Fixed known squeezing transported through the real cloning circuit
-- statement:
--   Let $N,M$ be positive integers with $N\le M$, let $\alpha\in\mathbb C$ be unknown, and use $[x_j,p_k]=i\delta_{jk}$ and $a_j=(x_j+ip_j)/\sqrt2$. Thus a vacuum quadrature has variance $1/2$. All implementations below are chosen independently of $\alpha$, and the conclusions hold for every $\alpha$.
--
--   Fix a known squeezing amount $r\in\mathbb R$ and known axis $\theta\in\mathbb R$. Let $Q$ be a one-mode squeezing unitary with real symplectic matrix $R(\theta)\operatorname{diag}(e^{-r},e^r)R(\theta)^T$, where $R$ is a plane rotation. Prepare the $N$ originals in $Q|\alpha\rangle$, all blanks in the corresponding squeezed vacuum, and the controlled idler with the corresponding conjugated-axis squeezing $ZQZ$ in quadrature coordinates, where $Z=\operatorname{diag}(1,-1)$. Along the squeezing axes this is the same squeezing on every auxiliary mode. These preparations are independent products.
--
--   The real inverse-$N$-splitter, gain-$M/N$ two-mode amplifier, and $M$-splitter circuit can be chosen before the unknown displacement. Its clone marginals are exactly
--
--   $$\rho_{r,\theta,\alpha}=Q D(\alpha)\tau_t D(\alpha)^\dagger Q^\dagger,\qquad t=\frac1N-\frac1M,\qquad \langle Q\alpha|\rho_{r,\theta,\alpha}|Q\alpha\rangle=\frac{MN}{MN+M-N}.$$
--
--   Here $D$ denotes displacement, $\tau_t$ the thermal density with mean photon number $t$, and $|Q\alpha\rangle$ abbreviates $Q|\alpha\rangle$. The joint squeeze preparation, the single-mode squeeze, and the real optical circuit have actual full-Fock unitary implementations.
--
--   This transports the coherent-state construction to a pure displaced squeezed family of fixed known squeezing. It requires control of the amplifier idler and makes no assertion for arbitrary unknown squeezing; $r=0$ recovers the coherent case.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 4, Final unnumbered extension

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, final extension: the real splitter circuit clones pure displaced
squeezed vacua of fixed KNOWN r and axis theta with the same fidelity. All blanks
and the controlled idler are correspondingly squeezed. The idler's conjugated
axis is forced by the dagger in Eq.(11); this does not configure an inaccessible
noise port of an off-the-shelf amplifier. At r=0 it is the coherent construction. -/
theorem fixed_known_squeezing_cloner (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (r theta : ℝ) (W : FockWeylSystem (M + 1)) (Wone : FockWeylSystem 1) :
    ∃ (U V : ModeUnitary (M + 1)) (Q : ModeUnitary 1),
      OpticalCircuitRealized W (serialGates N M hN hNM) U ∧
      FockCanonicalAction W U (circuitMatrix (serialGates N M hN hNM)) ∧
      FockCanonicalAction W V (jointSqueeze M r theta) ∧
      FockCanonicalAction Wone Q (singleSqueeze r theta) ∧
      (∀ a : ℂ, NormalizedCoherent (cloningAmplitudes N M a) ∧
        NormalizedCoherent (fun _ : Fin 1 => a) ∧
        let input := V (coherentProduct (cloningAmplitudes N M a))
        let rho := unitaryConjugation Q (displacedThermal Wone a (cloneNoise N M))
        ‖input‖ = 1 ∧ IsModeDensity (pureDensity (U input)) ∧
        (∀ l : Fin M, IsReducedDensity (pureDensity (U input))
          (firstModes M M (by omega) l) rho) ∧
        (inner ℂ (Q (coherentProduct (fun _ : Fin 1 => a))) (rho (Q (coherentProduct (fun _ : Fin 1 => a))))).re = cloneFidelity N M) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
