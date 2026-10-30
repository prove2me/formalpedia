-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_minimal_qubit_convergence
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.minimal_qubit_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:24:24.74893+00:00
-- url     : https://prove2.me/theorems/e78c3b9e-ed3d-487b-8e9a-f1310cb53327
-- title:
--   Concrete qubit minimal PBT converges
-- statement:
--   Let $N\ge1$ be the number of qubit ports. Alice and Bob share $N$ normalized Bell pairs. Put $\sigma_i=2^{-(N-1)}I_{A_{\ne i}}\otimes P^+_{A_iC}$, $\rho=\sum_i\sigma_i$, and $\Pi_i=\rho^{-1/2}\sigma_i\rho^{-1/2}$, with inverse taken on support. The physical failure effect is $\Delta=I-\sum_i\Pi_i$; Bob retains the announced port without correction. Let $p_N$ be the Choi-average success probability and $F_N$ the conditional entanglement fidelity. Writing $D_N=2^{-(N+2)}\sum_{\alpha\vdash N-1}(\sum_{\mu\in\alpha}\sqrt{d_\mu m_\mu})^2$ for (A10), where diagrams have height at most two and $\mu\in\alpha$ means one added box, we have
--
--   $$p_N=1-\frac{N+2}{2^{N+1}},\qquad F_N=\frac{D_N}{p_N},\qquad (F_N,p_N)\longrightarrow(1,1).$$
--
--   Moreover, there are constants $C>0$ and $N_0\ge1$ such that $|1-F_N|\le C/N$ for every $N\ge N_0$. This states convergence of the specified physical protocol. Here $d_\lambda$ is the dimension of the actual symmetric-group Specht module labelled by $\lambda$, and $m_\lambda$ is its Schur–Weyl multiplicity for local dimension $d$ (with $d=2$ in the qubit case).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 1, Abstract and §III A: concrete qubit minimal PBT and convergence

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Abstract, PDF p.1; §III A pp.7–11: concrete qubit Bell-resource mPBT,
its exact success and group-theoretic fidelity, and convergence with error O(1/N).
This uses conditional entanglement fidelity, not average pure-state fidelity. -/
theorem minimal_qubit_convergence :
    (∀ N : ℕ, 0 < N →
      IsPhysicalPBT (1 : AliceMatrix 2 N) (minimalEffects 2 N) ∧
      pbtSuccess (1 : AliceMatrix 2 N) (minimalEffects 2 N) =
        1 - ((N : ℝ) + 2) / 2 ^ (N + 1) ∧
      0 < pbtSuccess (1 : AliceMatrix 2 N) (minimalEffects 2 N) ∧
      conditionalFidelity (by norm_num : 0 < 2) (1 : AliceMatrix 2 N) (minimalEffects 2 N) =
        bellDeterministicFormula 2 N / (1 - ((N : ℝ) + 2) / 2 ^ (N + 1))) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      |1 - conditionalFidelity (by norm_num : 0 < 2)
        (1 : AliceMatrix 2 N) (minimalEffects 2 N)| ≤ C / N) ∧
    IsConvergent 2 (by norm_num) (fun _ => 1) (minimalEffects 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
