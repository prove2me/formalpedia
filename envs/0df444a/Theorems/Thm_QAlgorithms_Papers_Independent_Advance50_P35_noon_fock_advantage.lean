-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_noon_fock_advantage
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.noon_fock_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:46:24.52078+00:00
-- url     : https://prove2.me/theorems/7993f5d6-d431-4d16-b860-c6a510e63539
-- title:
--   NOON and Fock witnesses can beat classical and EPR readout
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. There exists $0\leq\kappa_0<1$ with $\kappa_1=1$ such that the normalized one-photon Fock state and normalized NOON state
--
--   $$|1\rangle_S,\qquad |N\rangle=\frac{|2\rangle_S|0\rangle_R+|0\rangle_S|2\rangle_R}{\sqrt2}$$
--
--   both have mean signal energy one and both satisfy
--
--   $$\chi(\bar\Phi\mid\rho)>C_c(\bar\Phi\mid1),\qquad\chi(\bar\Phi\mid\rho)>\chi(\bar\Phi\mid\rho_{\mathrm{epr}}(1,1,1)).$$
--
--   The same memory witnesses both comparisons for both inputs. No exact threshold for the phrase “low values” is introduced.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 12, §VII/Fig.7: NOON and Fock witnesses can outperform both classical and one-pair EPR readout

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

/-- Sec.VII/Fig.7 and (74)--(75), PDF p.12: BOTH concrete one-photon
witnesses can exceed both comparison curves, with no invented low-kappa threshold. -/
theorem noon_fock_advantage :
    ∃ M : LossMemory, M.p = 1 / 2 ∧ M.kappa1 = 1 ∧ M.kappa0 < 1 ∧
      IsDensity noonInput ∧ signalEnergy noonInput = 1 ∧
      IsDensity (fockInput 1) ∧ signalEnergy (fockInput 1) = 1 ∧
      classicalReadingCapacity M 1 < lossInformation M.kappa0 1 (1 / 2) noonInput ∧
      classicalReadingCapacity M 1 < lossInformation M.kappa0 1 (1 / 2) (fockInput 1) ∧
      lossInformation M.kappa0 1 (1 / 2) (eprInput 1 1) <
        lossInformation M.kappa0 1 (1 / 2) noonInput ∧
      lossInformation M.kappa0 1 (1 / 2) (eprInput 1 1) <
        lossInformation M.kappa0 1 (1 / 2) (fockInput 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
