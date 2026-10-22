-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_pure_key_monogamy
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.pure_key_monogamy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:59:40.824984+00:00
-- url     : https://prove2.me/theorems/24bc9495-b7c5-4b64-9d19-233eb5deb777
-- title:
--   Theorem 7: purified-state one-way secret-key monogamy
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABCE}$ be a normalized pure state. In each term the systems after the vertical bar belong to Eve; all four systems are retained and merely regrouped.
--
--   $$
--   K^{\leftarrow}(A:B\mid CE)_\rho+K^{\leftarrow}(A:C\mid BE)_\rho\le K^{\leftarrow}(A:BC\mid E)_\rho.
--   $$
--
--   This is pure-state secret-key monogamy. The first term gives both $C$ and $E$ to Eve.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 5, Theorem 7: purified-state one-way secret-key monogamy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.5, Theorem 7: globally pure ABCE; Eve holds CE in the first term, BE in the second, and E in the grouped term. -/
theorem pure_key_monogamy {A : Type} {B : Type} {C : Type} {E : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C] [Fintype E] [DecidableEq E] [Nonempty E]
    (rho : Op (A × (B × (C × E)))) (hrho : IsDensityMatrix rho) (hpure : IsPure rho) :
    keyLeft rho + keyLeft (groupACBE rho) ≤ keyLeft (groupABCE rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35
