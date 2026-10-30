-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_single_cell_beats_classical_capacity
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.single_cell_beats_classical_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:49:59.555716+00:00
-- url     : https://prove2.me/theorems/63f70bcd-a862-479c-9bd1-133d7d82744e
-- title:
--   Independent EPR detection can beat collective classical readout
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. For $n=5$, there exists an ideal memory with $0\leq\kappa_0<1$, $\kappa_1=1$ for which the one-pair lower bound
--
--   $$Q_1(\kappa_0,5)=1-h_2\!\left(\frac{1}{2[1+5(1-\sqrt{\kappa_0})]^2}\right)>C_c(\{\kappa_0,1\}\mid5).$$
--
--   An actual binary single-cell measurement on that fixed one-pair input achieves at least $Q_1$, and $Q_\infty\geq Q_1$. This is the existential crossing in Fig.11’s upper panel, without extending the advantage to every reflectivity.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 13, §VII/Fig.11 upper panel: independent EPR detection can beat collective classical readout

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

/-- Sec.VII/Fig.11 upper panel, PDF p.13: one-pair independent detection
at signal energy five can exceed collective classical readout. -/
theorem single_cell_beats_classical_capacity :
    ∃ M : LossMemory, M.p = 1 / 2 ∧ M.kappa1 = 1 ∧ M.kappa0 < 1 ∧
      classicalReadingCapacity M 5 < ENNReal.ofReal (eprLowerRate M.kappa0 1 5) ∧
      SingleCellAchievable M.kappa0 1 5 (eprLowerRate M.kappa0 1 5) ∧
      eprLowerRate M.kappa0 1 5 ≤ eprLimitRate M.kappa0 5 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
