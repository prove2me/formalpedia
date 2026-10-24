-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_equivalent_sdps_strongDuality
-- name    : QAlgorithms.Papers.Independent.Support50.P04.equivalent_sdps_strongDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:45:17.685274+00:00
-- url     : https://prove2.me/theorems/a35723b0-3285-4f59-abad-e66aca869373
-- title:
--   Equivalent primal and dual SDPs with strong duality
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Let $0<\varepsilon<1$. Let $J_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(|A|\Phi_A)$ be the unnormalized Choi matrix. Define $\Gamma(\rho)=\{\Lambda\succeq0:\Lambda\preceq\rho^T\otimes I_B,\ \operatorname{tr}\Lambda J_{\mathcal N}\ge1-\varepsilon\}$. Set $f(\mathcal N,\varepsilon)=\inf_{\rho\in\mathcal S(A)}\inf_{\Lambda\in\Gamma(\rho)}\sup_J\operatorname{tr}(\Lambda J)$, where the comparison Choi operators satisfy $J\succeq0$, $J^{T_A}\succeq0$, and $\operatorname{tr}_B J=I_A$. In the minimization program, $\rho$ is a density matrix, $\Lambda\in\Gamma(\rho)$, $\xi\succeq0$, $\Theta\succeq0$, and $\xi\otimes I_B\succeq\Lambda+\Theta^{T_A}$. In the maximization program, $\mu,\nu\ge0$, $J,R\succeq0$, $J^{T_A}\succeq0$, $\operatorname{tr}_B J\preceq I_A$, $\mu J_{\mathcal N}\preceq J+R$, and $\operatorname{tr}_B R\preceq\nu I_A$. Then
--
--   $$f(\mathcal N,\varepsilon)=f_{\mathrm{TNI}}(\mathcal N,\varepsilon)=\inf\operatorname{tr}\xi=\sup[\mu(1-\varepsilon)-\nu].$$
--
--   Here $f_{\mathrm{TNI}}$ permits $\operatorname{tr}_B J\preceq I_A$ in the inner comparison optimization. This gives both equivalent semidefinite formulations and equality of their values.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 21, Theorem 7, Eqs. (A3)–(A4)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.21–22, Theorem 7, Eqs.(A3)–(A4).
Both SDP formulations and strong duality are retained; the appendix's TNI comparison
maps have the same value as TP comparison channels. Printed n/nu is renamed nu.
The proof's false norm equality ||J_N||=|A| needs only <=|A|, not an added assumption. -/
theorem equivalent_sdps_strongDuality [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    metaValue N epsilon = metaValue N epsilon true ∧
    metaValue N epsilon = sdpMinValue N epsilon ∧
    metaValue N epsilon = sdpMaxValue N epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
