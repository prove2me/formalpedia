-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_idealCW_beam
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.idealCW_beam
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:04:13.484494+00:00
-- url     : https://prove2.me/theorems/c3860776-fca3-4749-a59e-3f2d67a96355
-- title:
--   Ideal CW beam: common-phase coherent copies
-- statement:
--   Consider the noiseless, one-sided continuous-wave laser in the ideal vacuum-input, linear, frequency-independent input-output model of Section II. The high-finesse, near-resonance and long-time conditions specify the regime of that ideal model; no physical approximation-error estimate is claimed. Let the decay rate be $\kappa\ge0$, packet duration $T>0$, and phase-zero intracavity amplitude $\alpha\ge0$. Put $a=\sqrt{\kappa T}\alpha$. Rectangular packets have centers $\tau+nT$ and normalized envelopes $T^{-1/2}$ on $|t-\tau-nT|<T/2$, where $\tau=z_0/c$ is arbitrary. The output is constructed by projecting $\beta(t)=\sqrt\kappa\alpha e^{i\phi}$ onto those packets and averaging the stationary intracavity Poisson ensemble's common phase.
--
--   For every finite number $N$ of packets its density is
--
--   $$
--   \rho_N(a)=\int_0^{2\pi}\left(|ae^{i\theta}\rangle\langle ae^{i\theta}|\right)^{\otimes N}\frac{d\theta}{2\pi}.
--   $$
--
--   This is a positive trace-class operator of trace one, and the integral exists in trace norm. Every constructed coherent product has its displayed full-Fock coefficients and norm one. The family is invariant under packet permutations and satisfies $\operatorname{tr}_{N+1}\rho_{N+1}(a)=\rho_N(a)$, with the partial trace represented by convergent occupation sums. If $a>0$ and $N\ge2$, then $\rho_N(a)\ne\rho_{\rm Pois}(a^2)^{\otimes N}$. The independent product also has its actual bounded tensor-matrix realization.
--
--   This compatible finite-window family describes an infinite CW beam without asserting a finite-energy global Fock vector. At $N=0$ the density is the scalar unit; at $a=0$ every packet is vacuum.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 8, IV; Eq.(13), PDF p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF pp.2–4, Eq.(13), restated p.8.
The stationary noiseless, vacuum-input CW model is constructed by idealBeam;
its computed packet projections give a=sqrt(kappa*T)*alpha. The conclusion
includes compatibility, permutation symmetry, and the explicit nonproduct claim.
No finite-energy global state of an infinite CW beam is claimed. -/
theorem idealCW_beam (kappa T tau alpha : ℝ) (hk : 0 ≤ kappa)
    (hT : 0 < T) (ha : 0 ≤ alpha) :
    let a := Real.sqrt (kappa * T) * alpha
    (∀ N, idealBeam kappa T tau alpha N = commonPhase a N ∧
      IsPacketDensity (commonPhase a N) ∧
      TraceIntegral phaseLaw
        (fun theta => packetProjector (fun _ : Fin N => (a : ℂ) * phase theta))
        (commonPhase a N)) ∧
    (∀ (N : ℕ) (z : Fin N → ℂ), Memℓp (packetCoefficients z) 2 ∧
      (∀ m, packetCoherent z m = packetCoefficients z m) ∧ ‖packetCoherent z‖ = 1) ∧
    (∀ N, discardLastPacket (commonPhase a (N + 1)) = commonPhase a N ∧
      (∀ m n, Summable (fun k : ℕ =>
        commonPhase a (N + 1) (packetBasis (Fin.snoc n k)) (Fin.snoc m k))) ∧
      HasPacketMatrix (discardLastPacket (commonPhase a (N + 1))) (fun m n => ∑' k : ℕ,
        commonPhase a (N + 1) (packetBasis (Fin.snoc n k)) (Fin.snoc m k))) ∧
    (∀ N (s : Equiv.Perm (Fin N)), permutePackets s (commonPhase a N) = commonPhase a N ∧
      HasPacketMatrix (permutePackets s (commonPhase a N))
        (fun m n => commonPhase a N (packetBasis (n ∘ s)) (m ∘ s))) ∧
    (∀ N, 2 ≤ N → 0 < a →
      commonPhase a N ≠ fullFockTensorPower (poissonDensity (a ^ 2)) N) ∧
    (∀ N, HasPacketMatrix (fullFockTensorPower (poissonDensity (a ^ 2)) N)
      (fun m n => ∏ i, poissonDensity (a ^ 2) (fockKet (n i)) (m i))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
