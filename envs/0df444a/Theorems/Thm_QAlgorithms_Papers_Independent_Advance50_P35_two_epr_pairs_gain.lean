-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_two_epr_pairs_gain
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.two_epr_pairs_gain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:47:48.745949+00:00
-- url     : https://prove2.me/theorems/2100e720-9fad-4433-b61d-05f2398434f8
-- title:
--   Two weak TMSV pairs can beat one at fixed signal energy
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. For an ideal equal-prior memory there exists $0\leq\kappa_0<1$ such that
--
--   $$\chi(\{\kappa_0,1\}\mid\rho_{\mathrm{epr}}(2,2,1))>\chi(\{\kappa_0,1\}\mid\rho_{\mathrm{epr}}(1,1,1)).$$
--
--   Both inputs are normalized with the same total mean signal energy one. The two-pair input is the tensor product of two TMSV states each carrying mean signal energy $1/2$. This is the comparison shown in Fig.10, without a claim that exact Holevo information is monotone in the number of pairs.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 13, §VII/Fig.10: two weak TMSV pairs can beat one at fixed total signal energy

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

/-- Sec.VII/Fig.10, PDF pp.12--13: existence of the two-versus-one gain
at FIXED total signal energy one, with half a photon per pair for s=2. -/
theorem two_epr_pairs_gain :
    ∃ M : LossMemory, M.p = 1 / 2 ∧ M.kappa1 = 1 ∧ M.kappa0 < 1 ∧
      IsDensity (eprInput 2 1) ∧ signalEnergy (eprInput 2 1) = 1 ∧
      IsDensity (eprInput 1 1) ∧ signalEnergy (eprInput 1 1) = 1 ∧
      lossInformation M.kappa0 1 (1 / 2) (eprInput 1 1) <
        lossInformation M.kappa0 1 (1 / 2) (eprInput 2 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
