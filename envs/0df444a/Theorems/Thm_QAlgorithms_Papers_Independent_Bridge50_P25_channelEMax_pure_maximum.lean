-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_channelEMax_pure_maximum
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.channelEMax_pure_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:11:21.851869+00:00
-- url     : https://prove2.me/theorems/24bbca72-d2c0-4daa-a972-c7fde4e290db
-- title:
--   Unnumbered II B: pure-input maximum for channel Emax
-- statement:
--   Let $T:M_{d_A}\to M_{d_B}$ be a quantum channel in positive finite dimensions. Define $E_{\max}(T)$ as the supremum of output max-relative entanglement over all density matrices $\rho_{RA}$ and all positive finite reference dimensions. There exists a unit vector $|\psi\rangle_{A'A}$ with $d_{A'}=d_A$ such that
--
--   $$E_{\max}(T)=E_{\max}^{A':B}((\mathrm{id}_{A'}\otimes T)(|\psi\rangle\langle\psi|)).$$
--
--   The state quantity minimizes the max-relative divergence in bits to separable density matrices. The input-size reference and pure state attain the original unrestricted supremum.
--
--   This establishes a genuine maximum, rather than only equality of two suprema.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 5, Unnumbered II B

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Unnumbered pure-input maximum, PDF p.5: a normalized pure optimizer with
reference ISOMORPHIC TO INPUT attains the original arbitrary-reference supremum. -/
theorem channelEMax_pure_maximum (T : Superop I J) (hT : IsChannel T) :
    ∃ psi : EuclideanSpace ℂ (I × I), ‖psi‖ = 1 ∧
      channelEMax T = eMax (idTensorSuperop T (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
