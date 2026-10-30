-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_classical_collective_gain
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.classical_collective_gain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:44:37.107293+00:00
-- url     : https://prove2.me/theorems/65bdb9e4-c78a-4927-bb5b-bb31597d0349
-- title:
--   Classical collective readout improves the single-cell rate
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. Define the source error-entropy rate by
--
--   $$P_c=\frac{1-\sqrt{1-e^{-n(\sqrt{\kappa_0}-\sqrt{\kappa_1})^2}}}{2},\qquad I_c=1-h_2(P_c).$$
--
--   For all $n\geq0$, $I_c(\bar\Phi\mid n)\leq C_c(\bar\Phi\mid n)$. For the plotted memory $(\kappa_0,\kappa_1)=(1/2,9/10)$, there exists $n\in(0,100)$ for which the inequality is strict. This states the collective gain reported in Fig.5 using the precise rate in Eq.(25), rather than identifying that expression with every measurement’s mutual information.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 11, §VI/Fig.5: classical collective readout improves the single-cell bound

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

/-- Sec.VI/Fig.5, PDF p.11, with the source's algebraic rate (25), PDF p.6.
The strict plotted gain is existential in 0<n<100, not universal. -/
theorem classical_collective_gain :
    (∀ (M : LossMemory), M.p = 1 / 2 → ∀ n : ℝ, 0 ≤ n →
      ENNReal.ofReal (classicalSingleRate M n) ≤ classicalReadingCapacity M n) ∧
    (∃ (M : LossMemory) (n : ℝ), M.kappa0 = 1 / 2 ∧ M.kappa1 = 9 / 10 ∧
      M.p = 1 / 2 ∧ 0 < n ∧ n < 100 ∧
      ENNReal.ofReal (classicalSingleRate M n) < classicalReadingCapacity M n) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
