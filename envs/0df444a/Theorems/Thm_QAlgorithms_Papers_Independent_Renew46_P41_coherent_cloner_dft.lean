-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_coherent_cloner_dft
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.coherent_cloner_dft
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:19:50.11215+00:00
-- url     : https://prove2.me/theorems/71b100d7-b7c9-49ac-9cf2-77a4882a4aa6
-- title:
--   Optimal coherent-state cloning by concentration, amplification, and distribution
-- statement:
--   Let $N,M$ be positive integers with $N\le M$, let $\alpha\in\mathbb C$ be unknown, and use $[x_j,p_k]=i\delta_{jk}$ and $a_j=(x_j+ip_j)/\sqrt2$. Thus a vacuum quadrature has variance $1/2$. All implementations below are chosen independently of $\alpha$, and the conclusions hold for every $\alpha$.
--
--   Start with $N$ independent copies of $|\alpha\rangle$, $M-N$ vacuum blanks, and a vacuum idler. There exist full oscillator unitaries realizing: the positive-sign $N$-mode Fourier mixing $F_N$, a two-mode amplifier of power gain $G=M/N$, and positive-sign $M$-mode Fourier mixing $F_M$. Here $(F_L)_{jk}=e^{2\pi i jk/L}/\sqrt L$. Concentration leaves the first mode in $|\sqrt N\alpha\rangle$ and all other modes in vacuum. The amplifier acts as $a_0\mapsto\sqrt G a_0+\sqrt{G-1}a_z^\dagger$ and $a_z\mapsto\sqrt{G-1}a_0^\dagger+\sqrt G a_z$.
--
--   Every clone has the same actual reduced density $\rho_\alpha=D(\alpha)\tau_tD(\alpha)^\dagger$, where $D$ is displacement, $\tau_t$ is the thermal density of mean photon number $t$, and
--
--   $$t=\frac1N-\frac1M,\qquad \operatorname{Cov}(\rho_\alpha)=\left(\frac12+t\right)I_2,\qquad \langle\alpha|\rho_\alpha|\alpha\rangle=\frac{MN}{MN+M-N}.$$
--
--   Its first moments are $(\sqrt2\operatorname{Re}\alpha,\sqrt2\operatorname{Im}\alpha)$. The joint unitary has the stated canonical Heisenberg action on every Weyl observable. This constructs a Gaussian cloner attaining the added-noise benchmark recalled in Eq.(1); it does not assert a fidelity bound over arbitrary non-Gaussian channels.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 1, Unnumbered main result; Eqs.(10)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1,3--4, Eqs.(10)--(12): a displacement-independent Fock-space
concentration/amplification/distribution dilation attains Eq.(1) and the stated
single-clone fidelity. No bound over arbitrary non-Gaussian cloners is asserted. -/
theorem coherent_cloner_dft (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (W : FockWeylSystem (M + 1)) (Wone : FockWeylSystem 1) :
    ∃ C A D : ModeUnitary (M + 1),
      FockCanonicalAction W C (dftConcentration N M) ∧
      FockCanonicalAction W A (twoModeAmplifierQuadratures (⟨0, by omega⟩ : Fin (M + 1))
        ⟨M, by omega⟩ ((M : ℝ) / N)) ∧
      FockCanonicalAction W D (dftDistribution M) ∧
      FockCanonicalAction W ((C.trans A).trans D) (dftClonerMatrix N M hN hNM) ∧
      Symplectic (dftClonerMatrix N M hN hNM) ∧
      (∀ a : ℂ, C (coherentProduct (cloningAmplitudes N M a)) =
        coherentProduct (fun k => if k.val = 0 then (Real.sqrt N : ℂ) * a else 0)) ∧
      ClonesCoherently Wone N M (cloningAmplitudes N M)
        (firstModes M M (by omega)) ((C.trans A).trans D) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
