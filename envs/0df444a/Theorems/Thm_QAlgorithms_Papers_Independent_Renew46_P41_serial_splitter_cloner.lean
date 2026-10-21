-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P41_serial_splitter_cloner
-- name    : QAlgorithms.Papers.Independent.Renew46.P41.serial_splitter_cloner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:23:57.784976+00:00
-- url     : https://prove2.me/theorems/997cea3e-2f2f-43cb-9c7c-0952d93525e3
-- title:
--   One amplifier and N+M−2 real beam splitters suffice
-- statement:
--   Let $N,M$ be positive integers with $N\le M$, let $\alpha\in\mathbb C$ be unknown, and use $[x_j,p_k]=i\delta_{jk}$ and $a_j=(x_j+ip_j)/\sqrt2$. Thus a vacuum quadrature has variance $1/2$. All implementations below are chosen independently of $\alpha$, and the conclusions hold for every $\alpha$.
--
--   Define a beam splitter $B_{kl}(\theta)$ to act as $\begin{pmatrix}\sin\theta&\cos\theta\\\cos\theta&-\sin\theta\end{pmatrix}$ on annihilation operators of modes $k,l$ and identically elsewhere. With one-based mode indices, define
--
--   $$U(L)=B_{L-1,L}\!\left(\arcsin\frac1{\sqrt2}\right)\cdots B_{1,2}\!\left(\arcsin\frac1{\sqrt L}\right).$$
--
--   Starting from $N$ equal coherent originals, $M-N$ independent vacuum blanks and a vacuum idler, the circuit applies $U(N)^\dagger$ on the originals, the two-mode amplifier of power gain $M/N$ on the concentrated signal and idler, and $U(M)$ on the signal/blank register. Every listed gate has a full-Fock unitary implementation. This circuit has precisely one amplifier and $N+M-2$ beam-splitter gates, and has the complete canonical action specified by that product.
--
--   For every $\alpha$, its clones have the same reduced state $D(\alpha)\tau_tD(\alpha)^\dagger$, where $D$ is displacement, $\tau_t$ is thermal with mean photon number $t=1/N-1/M$, quadrature variance $1/2+t$, the correct coherent first moments, and fidelity $MN/(MN+M-N)$.
--
--   This gives a sufficient physical gate count tied to an explicit list of gates, including the inverse concentration network. It is not a minimality assertion.
-- source:
--   Optimal cloning of coherent states with a linear amplifier and beam splitters, arXiv:quant-ph/0012046v1, PDF p. 3, Eqs.(13)–(16); summary p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P41

open scoped BigOperators

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeHilbert ModeOperator Quadrature PhaseVector numberKet IsModeDensity
   FockWeylSystem GaussianMoments unitaryConjugation thermalTensorDensity Symplectic)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, Eqs.(13)--(16): exactly the displayed real optical circuit,
with one amplifier and N+M-2 phase-free beam splitters. This is a sufficient
count; no minimality or necessity at N=M is asserted. -/
theorem serial_splitter_cloner (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (W : FockWeylSystem (M + 1)) (Wone : FockWeylSystem 1) :
    ∃ U : ModeUnitary (M + 1),
      OpticalCircuitRealized W (serialGates N M hN hNM) U ∧
      FockCanonicalAction W U (circuitMatrix (serialGates N M hN hNM)) ∧
      circuitMatrix (serialGates N M hN hNM) =
        modeMixingQuadratures (embedModes (n := M + 1) (splitterModes M)) *
          twoModeAmplifierQuadratures (⟨0, by omega⟩ : Fin (M + 1)) ⟨M, by omega⟩ ((M : ℝ) / N) *
          modeMixingQuadratures (embedModes (n := M + 1) (star (splitterModes N))) ∧
      ((serialGates N M hN hNM).filter (fun g => match g with
        | .beam _ _ _ => true | .amplifier _ _ _ => false)).length = N + M - 2 ∧
      ((serialGates N M hN hNM).filter (fun g => match g with
        | .beam _ _ _ => false | .amplifier _ _ _ => true)).length = 1 ∧
      ClonesCoherently Wone N M (cloningAmplitudes N M)
        (firstModes M M (by omega)) U := by sorry

end QAlgorithms.Papers.Independent.Renew46.P41

end
