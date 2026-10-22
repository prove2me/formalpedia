-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_partialIsometricEncoding_suffices
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.partialIsometricEncoding_suffices
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:18:59.989008+00:00
-- url     : https://prove2.me/theorems/35470663-a487-49bf-8a54-9c6969a2b6d1
-- title:
--   Partially isometric encoding suffices
-- statement:
--   Let $S$ and $C$ be nonzero finite-dimensional spaces and $\rho$ a density operator on $S$. Let $\mathcal A:\mathcal B(C)\to\mathcal B(S)$ be trace preserving and CP, and let $\mathcal E:\mathcal B(S)\to\mathcal B(C)$ be CP with $\operatorname{tr}\mathcal E(\rho)=1$. If $F_e(\rho,\mathcal A\mathcal E)>1-\eta$, then some partial isometry $W:S\to C$ satisfies
--
--   $$F_e(\rho,\mathcal A\circ[X\mapsto WXW^\dagger])>1-2\eta.$$
--
--   Normalization of $\mathcal E$ is required only at $\rho$; no global trace-nonincreasing condition is added.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 10, Theorem 4, Eqs.(89)–(90)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.10, Theorem 4, Eqs.(89)--(90): E is CP and normalized only on rho;
it need not be globally trace nonincreasing. W denotes an operator, and conjSuperop W
its single-Kraus CP operation. -/
theorem partialIsometricEncoding_suffices {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (A : Superop J I) (hA : IsChannel A) (E : Superop I J) (hE : FiniteCPMap E)
    (hnorm : (E rho).trace = 1) (eta : ℝ) (hgood : 1 - eta < fe rho (A ∘ E)) :
    ∃ W : Matrix J I ℂ, IsPartialIsometry W ∧
      1 - 2 * eta < fe rho (A ∘ conjSuperop W) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
