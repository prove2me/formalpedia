-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_gaussianSignalMoments
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.gaussianSignalMoments
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:52:18.666982+00:00
-- url     : https://prove2.me/theorems/6ef8b2bb-ecc0-4720-910d-bc740bf3f159
-- title:
--   §III: entropy and photon mean of the displaced thermal signals, (21)–(23)
-- statement:
--   On the full single-mode Fock space, let $N\ge0$ be finite and let $G_N$ be the circular complex Gaussian of variance $N$, with $G_0=\delta_0$. The coherent vector has coefficients $\langle m|\alpha\rangle=e^{-|\alpha|^2/2}\alpha^m/\sqrt{m!}$ and norm one. Construct $S_\alpha=\int|z+\alpha\rangle\langle z+\alpha|\,G_N(dz)$, and write $h(t)=(t+1)\log(t+1)-t\log t$, continuously interpreted at zero. These operators are normalized positive trace-class states, their coefficients are the indicated integrals, and
--
--   $$H(S_\alpha)=h(N),\qquad \operatorname{Tr}(S_\alpha a^\dagger a)=N+|\alpha|^2.$$
--
--   Also $S_0$ is the thermal state with diagonal $(N/(N+1))^m/(N+1)$. This result retains the coherent-projector endpoint $N=0$ without a photon cutoff.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 8, §III: entropy and photon mean of the displaced thermal signals, (21)–(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section III, PDF p.8, (20)-(23). Density normalization, the concrete integral
realization, full coherent coefficients, entropy and photon mean are conclusions.
N=0 is the coherent projector; no division by zero in a Gaussian density. -/
theorem gaussianSignalMoments (N : ℝ) (hN : 0 ≤ N) :
    (∀ alpha : ℂ, ∃ psi : Hilbert ℕ,
      (∀ m, psi m = QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient alpha m) ∧ ‖psi‖ = 1) ∧
    (∀ alpha : ℂ, constrainedCqDensity (gaussianSignal N alpha) ∧
      (∀ i j, constrainedCqCoefficient (gaussianSignal N alpha) i j =
        ∫ z : ℂ, QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient (z + alpha) i *
          star (QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient (z + alpha) j) ∂gaussian N) ∧
      constrainedCqEntropy (gaussianSignal N alpha) = ENNReal.ofReal (h N) ∧
      constrainedCqPhotonMean (gaussianSignal N alpha) = ENNReal.ofReal (N + Complex.normSq alpha)) ∧
    gaussianSignal N 0 = constrainedCqThermal N ∧
    (∀ i j, constrainedCqCoefficient (constrainedCqThermal N) i j =
      if i = j then (((N / (N + 1)) ^ i / (N + 1) : ℝ) : ℂ) else 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
