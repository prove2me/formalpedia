-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_quantum_classical_separation
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.quantum_classical_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:40:14.083984+00:00
-- url     : https://prove2.me/theorems/04e407df-7844-4fac-9fe5-627557049668
-- title:
--   Quantum and classical reading capacities are separated
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. There exists an ideal memory with $\kappa_1=1$ and $0\leq\kappa_0<1$ for which the one-pair TMSV input $\rho_{\mathrm{epr}}(1,1,1)$ is normalized, nonclassical and has mean signal energy one, and
--
--   $$C_c(\bar\Phi\mid1)<\chi(\bar\Phi\mid\rho_{\mathrm{epr}}(1,1,1))\leq C(\bar\Phi\mid1).$$
--
--   In particular $C(\bar\Phi\mid1)>C_c(\bar\Phi\mid1)$. This is an existential separation in the product-across-cells model, without a formula for the quantum optimum.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 1, Abstract and §VII: separation of quantum and classical reading capacities

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

/-- Abstract, PDF p.1; Sec.VII, pp.11--12/Fig.7: a concrete one-photon
nonclassical witness separates the two optimized capacities. -/
theorem quantum_classical_separation :
    ∃ M : LossMemory, M.p = 1 / 2 ∧ M.kappa1 = 1 ∧
      M.kappa0 < 1 ∧
      IsDensity (eprInput 1 1) ∧ signalEnergy (eprInput 1 1) = 1 ∧
      ¬ IsClassicalCellTransmitter (eprInput 1 1) ∧
      classicalReadingCapacity M 1 < lossInformation M.kappa0 M.kappa1 M.p (eprInput 1 1) ∧
      classicalReadingCapacity M 1 < quantumReadingCapacity M 1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
