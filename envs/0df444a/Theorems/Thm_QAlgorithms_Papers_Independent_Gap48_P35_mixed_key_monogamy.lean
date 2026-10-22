-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P35_mixed_key_monogamy
-- name    : QAlgorithms.Papers.Independent.Gap48.P35.mixed_key_monogamy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:00:27.568644+00:00
-- url     : https://prove2.me/theorems/5d07b5cb-a53c-4aa6-954d-d36fa0017893
-- title:
--   §III unnumbered, Eq. (12): stronger mixed-state secret-key inequality
-- statement:
--   All systems are finite nonzero-dimensional complex quantum systems. Density states are positive semidefinite with trace one, and $S$ is von Neumann entropy in bits. Write $E_f$ for formation, $I^{\leftarrow}$ for maximal Holevo correlation measured on the second party, $E_C$ for asymptotic singlet preparation cost, $E_D$ for EPR distillation rate, $C_D$ for net common randomness, and $K$ for secret-key rate. A left arrow means communication from the second legitimate party to the first. Key secrecy includes all public transcripts. Asymptotic tasks use independent copies, vanishing error and no extra initially shared resource.
--
--   Let $\rho_{ABCE}$ be any density state, possibly mixed. Only the first term discards $C$. The second gives both $B$ and $E$ to Eve, while the right side lets $BC$ cooperate.
--
--   $$
--   K^{\leftarrow}(A:B\mid E)_{\operatorname{Tr}_C\rho}+K^{\leftarrow}(A:C\mid BE)_\rho\le K^{\leftarrow}(A:BC\mid E)_\rho.
--   $$
--
--   This is the stronger mixed-state inequality and imposes no global purity assumption.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, PDF p. 5, §III unnumbered, Eq. (12): stronger mixed-state secret-key inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open Information100.P21 (Op)

open Information100.P08 (IsPure formation measuredCorrelation)

open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF p.5, Eq.(12): arbitrary mixed ABCE. Only the FIRST term traces C away; the second gives B to Eve and the third groups BC. -/
theorem mixed_key_monogamy {A : Type} {B : Type} {C : Type} {E : Type}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C] [Fintype E] [DecidableEq E] [Nonempty E]
    (rho : Op (A × (B × (C × E)))) (hrho : IsDensityMatrix rho) :
    keyLeft (dropC rho) + keyLeft (groupACBE rho) ≤ keyLeft (groupABCE rho) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P35
