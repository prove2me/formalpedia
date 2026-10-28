-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_optimal_complementary_slackness
-- name    : QAlgorithms.Papers.Independent.Support50.P04.optimal_complementary_slackness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:46:04.30493+00:00
-- url     : https://prove2.me/theorems/5775527f-812d-4bc2-98e5-ced194bba831
-- title:
--   All eight optimal complementary-slackness relations
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Let $0<\varepsilon<1$. Let $J_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(|A|\Phi_A)$ be the unnormalized Choi matrix. Define $\Gamma(\rho)=\{\Lambda\succeq0:\Lambda\preceq\rho^T\otimes I_B,\ \operatorname{tr}\Lambda J_{\mathcal N}\ge1-\varepsilon\}$. Set $f(\mathcal N,\varepsilon)=\inf_{\rho\in\mathcal S(A)}\inf_{\Lambda\in\Gamma(\rho)}\sup_J\operatorname{tr}(\Lambda J)$, where the comparison Choi operators satisfy $J\succeq0$, $J^{T_A}\succeq0$, and $\operatorname{tr}_B J=I_A$. In the minimization program, $\rho$ is a density matrix, $\Lambda\in\Gamma(\rho)$, $\xi\succeq0$, $\Theta\succeq0$, and $\xi\otimes I_B\succeq\Lambda+\Theta^{T_A}$. In the maximization program, $\mu,\nu\ge0$, $J,R\succeq0$, $J^{T_A}\succeq0$, $\operatorname{tr}_B J\preceq I_A$, $\mu J_{\mathcal N}\preceq J+R$, and $\operatorname{tr}_B R\preceq\nu I_A$. Assume the displayed feasible minimization and maximization variables are optimal: $\operatorname{tr}\xi=f=\mu(1-\varepsilon)-\nu$. Then all eight relations hold:
--
--   $$\begin{gathered}\operatorname{tr}\rho=1,\quad\operatorname{tr}(\Lambda J_{\mathcal N})=1-\varepsilon,\quad(\rho^T\otimes I_B)R=\Lambda R,\\(\xi\otimes I_B)J=(\Lambda+\Theta^{T_A})J,\quad\nu\rho=\operatorname{tr}_B(R^{T_A})\rho,\quad J^{T_A}\Theta=0,\\(\operatorname{tr}_B J)\xi=\xi,\quad\mu J_{\mathcal N}\Lambda=(J+R)\Lambda.\end{gathered}$$
--
--   These characterize relations between actual optimal solutions, not arbitrary feasible variables.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 22, Eqs. (A9)–(A16)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.22, Eqs.(A9)–(A16): ALL eight relations for
optimal feasible solutions. The T_A in (A13) is visible in the PDF but lost by
extraction; implicit identity tensor factors are explicit below. -/
theorem optimal_complementary_slackness [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (rho xi : Matrix A A ℂ) (Lambda Theta J R : Matrix (A × B) (A × B) ℂ)
    (mu nu : ℝ) (hmin : SdpMinFeasible N epsilon rho xi Lambda Theta)
    (hmax : SdpMaxFeasible N mu nu J R)
    (hminopt : xi.trace.re = metaValue N epsilon)
    (hmaxopt : mu * (1-epsilon) - nu = metaValue N epsilon) :
    rho.trace = 1 ∧
    (Lambda * QAlgorithms.Papers.Independent.Information100.P34.choi N).trace.re = 1-epsilon ∧
    Matrix.kronecker rho.transpose (1 : Matrix B B ℂ) * R = Lambda * R ∧
    Matrix.kronecker xi (1 : Matrix B B ℂ) * J = (Lambda + QAlgorithms.Entanglement.partialTransposeFirst Theta) * J ∧
    (nu : ℂ) • rho = traceRight (QAlgorithms.Entanglement.partialTransposeFirst R) * rho ∧
    QAlgorithms.Entanglement.partialTransposeFirst J * Theta = 0 ∧
    traceRight J * xi = xi ∧
    (mu : ℂ) • (QAlgorithms.Papers.Independent.Information100.P34.choi N * Lambda) = (J + R) * Lambda := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
