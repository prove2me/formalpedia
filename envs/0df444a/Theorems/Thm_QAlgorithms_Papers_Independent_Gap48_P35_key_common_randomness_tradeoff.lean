-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_key_common_randomness_tradeoff
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.key_common_randomness_tradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:01:21.876739+00:00
-- url     : https://prove2.me/theorems/c5b1aae1-d6ed-4010-9d8f-a3512cbdafe2
-- title:
--   §III unnumbered: secret key versus net common randomness
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABC}$ be any density state. In the key task $C$ is Eve; in the second task $C$ is a legitimate party, and the right side lets $BC$ cooperate.
--
--   $$
--   K^{\leftarrow}(A:B\mid C)_\rho+C_D^{\leftarrow}(\rho_{AC})\le C_D^{\leftarrow}(\rho_{A:BC}).
--   $$
--
--   The common randomness is net of communication, and the grouping $A:BC$ retains both factors.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 5, §III unnumbered: secret key versus net common randomness

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.5, §III following Eq.(12): key on AB secret against C, plus net common randomness on AC, bounded by net common randomness on A:BC. -/
theorem key_common_randomness_tradeoff {A : Type} {B : Type} {C : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) :
    keyLeft rho + commonLeft (marginalRB rho) ≤ commonLeft rho := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35
