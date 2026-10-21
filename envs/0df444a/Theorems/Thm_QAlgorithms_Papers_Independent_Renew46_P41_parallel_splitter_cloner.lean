-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_parallel_splitter_cloner
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.parallel_splitter_cloner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:24:38.641548+00:00
-- url     : https://prove2.me/theorems/6dd1398b-e7b5-4584-9bfc-47119f26c2cb
-- title:
--   Distributed amplification and recombination attain the clone benchmark
-- statement:
--   Let $N,M$ be positive integers with $N\le M$, let $\alpha\in\mathbb C$ be unknown, and use $[x_j,p_k]=i\delta_{jk}$ and $a_j=(x_j+ip_j)/\sqrt2$. Thus a vacuum quadrature has variance $1/2$. All implementations below are chosen independently of $\alpha$, and the conclusions hold for every $\alpha$.
--
--   Use $N$ independent banks. Each has one coherent original, $M-1$ vacuum blanks and a vacuum idler $a_{z,k}$. Amplify every original by power gain $M/N$, apply the real $M$-splitter $U(M)$ to each amplified signal and its blanks, and for each column $l$ apply $U(N)^\dagger$ across the $N$ bank outputs. The first output of each recombination is a clone; the other $N-1$ are waste. There is a full-Fock unitary implementing every listed gate and their composition.
--
--   Writing $d_{k,l}=\sum_{j=1}^{M-1}U(M)_{lj}b_{k,j}$ for the noise from the SAME vacuum inputs in bank $k$, the clone operator is
--
--   $$a_l''=\sum_{k=1}^N\left(\frac{a_k}{N}+\sqrt{\frac{M-N}{MN^2}}\,a_{z,k}^\dagger+\frac{d_{k,l}}{\sqrt N}\right),\qquad \operatorname{Var}(x_{d_{k,l}})=\operatorname{Var}(p_{d_{k,l}})=\frac{M-1}{2M}.$$
--
--   All clones have equal actual reduced density $D(\alpha)\tau_tD(\alpha)^\dagger$, with $D$ displacement, thermal occupation $t=1/N-1/M$, variance $1/2+t$, correct coherent first moments and fidelity $MN/(MN+M-N)$. There are $M(N-1)$ specified waste output modes, each centered at zero.
--
--   This is a second concrete optimal Gaussian architecture. The different $d_{k,l}$ in a fixed bank share vacuum inputs and are not assumed independent. Centered waste means noise-only, not noise-free.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 4, Eqs.(17)–(21), PDF pp.3–4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, Eqs.(17)--(21): the alternative distributed architecture
has the full stated operator action and attains the same clone density and noise.
Its M(N-1) waste outputs have zero first moments, not zero noise. -/
theorem parallel_splitter_cloner (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (W : FockWeylSystem (N * (M + 1))) (Wone : FockWeylSystem 1) :
    ∃ U : ModeUnitary (N * (M + 1)),
      OpticalCircuitRealized W (parallelGates N M hN hNM) U ∧
      FockCanonicalAction W U (circuitMatrix (parallelGates N M hN hNM)) ∧
      (∀ (l : Fin M) (p : Fin 2) j,
        circuitMatrix (parallelGates N M hN hNM) (parallelCloneSlot N M hN l, p) j =
          parallelCloneRow N M hN hNM l p j) ∧
      (∀ l : Fin M, (∑ j : Fin (M + 1), (splitterNoiseCoefficient M l j) ^ 2) / 2 =
        ((M : ℝ) - 1) / (2 * M)) ∧
      ClonesCoherently Wone N M (parallelAmplitudes N M) (parallelCloneSlot N M hN) U ∧
      Fintype.card (Fin (N - 1) × Fin M) = M * (N - 1) ∧
      (∀ a : ℂ, ∀ k : Fin (N - 1), ∀ l : Fin M,
        ∃ (rho : ModeOperator 1) (V : Matrix (Quadrature 1) (Quadrature 1) ℝ),
          IsReducedDensity (pureDensity (U (coherentProduct (parallelAmplitudes N M a))))
            (parallelWasteSlot N M k l) rho ∧ PhysicalGaussian Wone rho 0 V) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
