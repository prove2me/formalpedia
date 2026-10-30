-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_total_energy_separation
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.total_energy_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:50:40.329581+00:00
-- url     : https://prove2.me/theorems/417f6ed1-6b4f-4f85-857b-29bbc87a4971
-- title:
--   A quantum advantage survives counting reference energy
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. For every arbitrary-prior binary pure-loss memory and $n\geq0$, let $C_c^{\mathrm{tot}}(\widetilde\Phi\mid n)$ optimize classical transmitters under exact signal-plus-reference photon number $n$. Then
--
--   $$C_c^{\mathrm{tot}}(\widetilde\Phi\mid n)=C_c(\widetilde\Phi\mid n)=\chi(\widetilde\Phi\mid|\sqrt n\rangle\langle\sqrt n|).$$
--
--   This optimizer has one signal and no reference. Furthermore, for total budget five there exists an equal-prior ideal memory $\{\kappa_0,1\}$ with $0\leq\kappa_0<1$ such that
--
--   $$Q_1(\kappa_0,5/2)>C_c^{\mathrm{tot}}(\{\kappa_0,1\}\mid5).$$
--
--   The normalized one-pair TMSV witness has signal energy $5/2$, reference energy $5/2$, and total energy five, and a single-cell measurement achieves at least the displayed lower bound. This matches Fig.11’s lower panel and its continuation on p.14.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 13, §VII/Fig.11 lower panel: advantage with signal-plus-reference energy counted

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

/-- Sec.VII/Fig.11 lower panel, PDF pp.13--14: total-budget classical
invariance AND a one-pair quantum witness with energy 5/2 in EACH subsystem. -/
theorem total_energy_separation :
    (∀ (M : LossMemory) (n : ℝ), 0 ≤ n →
      classicalTotalCapacity M n = classicalReadingCapacity M n ∧
        cellTotalPhotonEnergy (coherentInput n) = ENNReal.ofReal n ∧
        lossInformation M.kappa0 M.kappa1 M.p (coherentInput n) = classicalTotalCapacity M n) ∧
    (∃ M : LossMemory, M.p = 1 / 2 ∧ M.kappa1 = 1 ∧ M.kappa0 < 1 ∧
      IsDensity (eprInput 1 (5 / 2)) ∧
      signalEnergy (eprInput 1 (5 / 2)) = ENNReal.ofReal (5 / 2) ∧
      cellTotalPhotonEnergy (eprInput 1 (5 / 2)) = 5 ∧
      classicalTotalCapacity M 5 < ENNReal.ofReal (eprLowerRate M.kappa0 1 (5 / 2)) ∧
      SingleCellAchievable M.kappa0 1 (5 / 2) (eprLowerRate M.kappa0 1 (5 / 2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
