-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_epr_finite_pair_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.epr_finite_pair_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:48:38.643408+00:00
-- url     : https://prove2.me/theorems/27dcedb7-0d99-4633-b80e-9141538a9037
-- title:
--   Finite-pair EPR error and achievable-rate bounds
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. Let $\kappa_1=1$, $0\leq\kappa_0<1$, $s\geq1$ be an integer, and $n\geq0$. Fix the normalized $s$-pair TMSV input of total signal energy $n$, with energy $n/s$ per pair. Let $P_s$ be its minimum binary error over all single-cell measurements. Put
--
--   $$\Theta_s=\frac{1}{2[1+(n/s)(1-\sqrt{\kappa_0})]^{2s}},\qquad Q_s=1-h_2(\Theta_s),\qquad I_{\mathrm{epr}}=1-h_2(P_s).$$
--
--   Then $P_s,\Theta_s\in[0,1/2]$ and
--
--   $$P_s\leq\Theta_s,\qquad I_{\mathrm{epr}}\geq Q_s.$$
--
--   There exists a binary single-cell POVM whose actual mutual information is at least $Q_s$; its outcomes may be read independently across cells. The source-defined $I_{\mathrm{epr}}$ is used as an error-entropy rate without an assumed binary symmetric measurement channel.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 13, §VII Eqs.(77)–(78): finite-pair EPR error and readable-rate bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Sec.VII, PDF p.13, (76)--(78): optimal error of the FIXED EPR input,
its error-entropy bound, and an actual one-cell measurement achieving that bound. -/
theorem epr_finite_pair_bounds (kappa0 n : ℝ) (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1)
    (hn : 0 ≤ n) (s : ℕ) (hs : 1 ≤ s) :
    IsDensity (eprInput s n) ∧ signalEnergy (eprInput s n) = ENNReal.ofReal n ∧
      eprError kappa0 s n ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      thetaFinite kappa0 s n ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      eprError kappa0 s n ≤ thetaFinite kappa0 s n ∧
      eprLowerRate kappa0 s n ≤ eprErrorRate kappa0 s n ∧
      SingleCellAchievable kappa0 s n (eprLowerRate kappa0 s n) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
