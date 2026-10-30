-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_ideal_one_photon_epr_advantage
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.ideal_one_photon_epr_advantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:45:31.754897+00:00
-- url     : https://prove2.me/theorems/7b3280f6-44f9-4a89-af6d-fc918b8a1848
-- title:
--   One TMSV pair beats classical capacity for ideal one-photon memories
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. For every $0\leq\kappa_0<1$, take $\kappa_1=1$ and the single-pair TMSV input with one mean signal photon,
--
--   $$|\xi\rangle=\sum_{m=0}^{\infty}2^{-(m+1)/2}|m\rangle_S|m\rangle_R.$$
--
--   Its density is normalized, its signal energy is one, and
--
--   $$\chi(\bar\Phi\mid|\xi\rangle\langle\xi|)>C_c(\bar\Phi\mid1).$$
--
--   This is the universal ideal-memory slice stated alongside Fig.7; coincident channels at $\kappa_0=1$ are excluded.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 11, §VII/Fig.7: one TMSV pair beats all classical transmitters for ideal one-photon memories

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

/-- Sec.VII/Fig.7, PDF pp.11--12: the source's universal ideal-memory slice
at n=1; kappa0=1 is excluded because strict gain then fails. -/
theorem ideal_one_photon_epr_advantage (M : LossMemory)
    (hp : M.p = 1 / 2) (hideal : M.kappa1 = 1) (hstrict : M.kappa0 < 1) :
    IsDensity (eprInput 1 1) ∧ signalEnergy (eprInput 1 1) = 1 ∧
      classicalReadingCapacity M 1 < lossInformation M.kappa0 1 (1 / 2) (eprInput 1 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
