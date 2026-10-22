-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_93
-- name    : QRepeaterBench.Dephasing.eq_93
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:34.890309+00:00
-- url     : https://prove2.me/theorems/d2e9e0c7-47b3-440f-9419-af3a716b9d2d
-- title:
--   Eq. (93) — Tr(ρ_{P_d} log₂ σ̃) = −log₂ d, with the support of ρ_{P_d} inside the support of σ̃
-- statement:
--   Let $d\ge2$ and $p\in[0,1]$. The support of the Choi matrix $\rho_{\mathcal P_d}$ is contained in the support of $\tilde\sigma$ (equivalently, the kernel of $\tilde\sigma$ is contained in the kernel of $\rho_{\mathcal P_d}$), and
--
--   $$\mathrm{Tr}(\rho_{\mathcal P_d}\log_2\tilde\sigma)=\sum_{i=0}^{d-1}\langle ii|\rho_{\mathcal P_d}|ii\rangle\log_2\frac1d=-\log_2 d .$$
--
--   This is the second term of the relative entropy $S(\rho_{\mathcal P_d}\|\tilde\sigma)$.
--
--   **Formalization Note** $\tilde\sigma$ has rank $d$ in dimension $d^2$, so $\log_2\tilde\sigma$ is taken on its support: it is the functional calculus of $\log_2$ with $\log_2 0=0$. The support inclusion, implicit on the page, is stated explicitly because it is what makes $S(\rho_{\mathcal P_d}\|\tilde\sigma)$ finite.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 11, Eq. (93)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_93 (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : LinearMap.ker (sigmaTilde d p).mulVecLin ≤ LinearMap.ker (choi d (dephasing d p)).mulVecLin ∧ (choi d (dephasing d p) * cfc (Real.logb 2) (sigmaTilde d p)).trace.re = -Real.logb 2 (d : ℝ) := by sorry
end QRepeaterBench.Dephasing
