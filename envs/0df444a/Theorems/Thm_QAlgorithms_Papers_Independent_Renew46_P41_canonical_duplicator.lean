-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_canonical_duplicator
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.canonical_duplicator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:20:58.498771+00:00
-- url     : https://prove2.me/theorems/257d6bbe-c487-4f1a-99a0-44e46326747d
-- title:
--   Canonical three-mode duplicator and phase-conjugated ancillary mean
-- statement:
--   Use three oscillator modes $(0,1,z)$ with $[x_j,p_k]=i\delta_{jk}$ and vacuum quadrature variance $1/2$. There is an input-independent unitary whose canonical Heisenberg action is
--
--   $$\begin{aligned}x_0''&=x_0+(x_1+x_z)/\sqrt2,&p_0''&=p_0+(p_1-p_z)/\sqrt2,\\ x_1''&=x_0+(-x_1+x_z)/\sqrt2,&p_1''&=p_0+(-p_1-p_z)/\sqrt2,\\ x_z'&=x_0+\sqrt2x_z,&p_z'&=-p_0+\sqrt2p_z.\end{aligned}$$
--
--   These identities are specified on all Weyl observables and preserve the canonical commutators. For every coherent input $|\alpha\rangle$ on mode 0 and independent vacuum on modes 1 and $z$, the two clones have identical reduced density $D(\alpha)\tau_{1/2}D(\alpha)^\dagger$. Here $D$ is displacement and $\tau_{1/2}$ is the thermal state of mean photon number $1/2$. Each clone has mean $(\sqrt2\operatorname{Re}\alpha,\sqrt2\operatorname{Im}\alpha)$, quadrature variance $1$, and coherent-state fidelity $2/3$. The ancillary reduced density is Gaussian and centered at $(\sqrt2\operatorname{Re}\alpha,-\sqrt2\operatorname{Im}\alpha)$.
--
--   This is an actual three-mode unitary construction with single-mode reduced densities. The ancillary output is not declared to be a pure phase-conjugated coherent state.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 2, Eq.(7) and adjacent text

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Eq.(7) and adjacent text: the full three-mode canonical operator
identity and its coherent-input performance. The ancillary state is centered at
the conjugated amplitude; it is not asserted to be a pure conjugated coherent state. -/
theorem canonical_duplicator (W : FockWeylSystem 3) (Wone : FockWeylSystem 1) :
    ∃ U : ModeUnitary 3,
      FockCanonicalAction W U duplicatorMatrix ∧ Symplectic duplicatorMatrix ∧
      ClonesCoherently Wone 1 2 (cloningAmplitudes 1 2)
        (firstModes 2 2 (by omega)) U ∧
      (∀ a : ℂ, ∃ rho : ModeOperator 1,
        IsReducedDensity (pureDensity (U (coherentProduct (cloningAmplitudes 1 2 a)))) 2 rho ∧
        ∃ V : Matrix (Quadrature 1) (Quadrature 1) ℝ,
          PhysicalGaussian Wone rho (coherentMean (star a)) V) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
