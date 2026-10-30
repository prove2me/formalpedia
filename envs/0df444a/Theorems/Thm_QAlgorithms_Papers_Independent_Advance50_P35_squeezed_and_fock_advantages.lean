-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_squeezed_and_fock_advantages
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.squeezed_and_fock_advantages
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:47:00.428889+00:00
-- url     : https://prove2.me/theorems/b938da00-c76b-40cc-9699-997f64149ac2
-- title:
--   Orthogonal squeezing gives an unassisted advantage; Fock input can do better
-- statement:
--   The memory uses vacuum pure-loss channels with distinct transmissivities in $[0,1]$. A transmitter may jointly entangle its finite number $s\geq1$ of signal modes and $r\geq0$ reference modes; the references bypass the cell. Unless total energy is expressly mentioned, $n$ is the exact finite mean of the sum of the signal photon numbers, with no reference-energy constraint. The same transmitter is repeated independently across cells, and the block outputs may be measured collectively. Priors are fixed, and information is in bits. Write $\bar\Phi=\{\kappa_0,\kappa_1\}$ for the equal-prior binary memory, $C_c(\bar\Phi\mid n)$ for its classical reading capacity, and $\chi(\bar\Phi\mid\rho)$ for the conditional output Holevo information. Classical transmitters are arbitrary Borel probability mixtures of multimode coherent product states, including singular laws. At $n=1$ and $\kappa_0=0$, let $V_{\mathrm{sq}}(\kappa_1)$ be the supremum of $\chi$ over the real squeezed-coherent family $D(\alpha)S(\xi)|0\rangle$, with squeezing orthogonal to the real displacement, parametrized by $\xi\geq0$ and $\alpha^2+\sinh^2\xi=1$. Each constructed input is normalized with mean signal energy one. Then
--
--   $$\exists\kappa_1\in(0,1):\quad V_{\mathrm{sq}}(\kappa_1)>C_c(\{0,\kappa_1\}\mid1),$$
--
--   and
--
--   $$\exists\kappa_1\in(0,1]:\quad\chi(\{0,\kappa_1\}\mid|1\rangle\langle1|)>V_{\mathrm{sq}}(\kappa_1).$$
--
--   This retains both reported crossings of Fig.9. The family is defined by full Fock coefficients, and its supremum is not the unrestricted quantum capacity.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 12, §VII/Fig.9: squeezing gives an unassisted advantage, and Fock input can do better

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

/-- Sec.VII/Fig.9, PDF p.12: both reported crossings for the actual
orthogonally squeezed family at n=1. The family optimum is not quantum capacity. -/
theorem squeezed_and_fock_advantages :
    (∀ alpha xi : ℝ, 0 ≤ xi → alpha ^ 2 + Real.sinh xi ^ 2 = 1 →
      IsDensity (squeezedInput alpha xi) ∧ signalEnergy (squeezedInput alpha xi) = 1) ∧
    (∃ M : LossMemory, M.p = 1 / 2 ∧ M.kappa0 = 0 ∧
      0 < M.kappa1 ∧ M.kappa1 < 1 ∧ classicalReadingCapacity M 1 < squeezedValue M.kappa1) ∧
    (∃ kappa1 : ℝ, 0 < kappa1 ∧ kappa1 ≤ 1 ∧
      squeezedValue kappa1 < lossInformation 0 kappa1 (1 / 2) (fockInput 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
