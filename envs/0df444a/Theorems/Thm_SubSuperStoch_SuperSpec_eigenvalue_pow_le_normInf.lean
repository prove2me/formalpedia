-- Prove2me | Theorems.Thm_SubSuperStoch_SuperSpec_eigenvalue_pow_le_normInf
-- name    : SubSuperStoch.SuperSpec.eigenvalue_pow_le_normInf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:58.015761+00:00
-- url     : https://prove2.me/theorems/d1c3dc94-3232-4b0e-93f3-ab48d10a8393
-- title:
--   Proof of Theorem 2.2, p. 5 (used on p. 9) — every eigenvalue μ of A satisfies |μ|^m ≤ ‖A^m‖_∞
-- statement:
--   Let $A$ be a real $n\times n$ matrix and $m$ a natural number. Every complex eigenvalue $\mu$ of $A$ satisfies
--   $$|\mu|^m\le\|A^m\|_\infty .$$
--   Equivalently, $\rho(A)^m=\rho(A^m)\le\|A^m\|_\infty$.
--
--   The proof of Theorem 2.2 invokes this as "the known facts $\rho(F^{|\mathcal C^*|+1})=\rho^{|\mathcal C^*|+1}(F)$ and $\rho(F^{|\mathcal C^*|+1})\le\|F^{|\mathcal C^*|+1}\|_\infty$", and the proof of Theorem 2.6 uses it in the step "Which in turn means that" to pass from the norm bound on $F^{|\mathcal C^*|+1}$ to the spectral radius of $F$.
--
--   **Formalization Note** Eigenvalues are the spectrum of $A$ regarded as a complex matrix; the infinity norm is the maximal absolute row sum. The statement is for an arbitrary real square matrix and an arbitrary exponent $m$, of which the paper uses $m=|\mathcal C^*|+1$.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 5, proof of Theorem 2.2, last sentence; used on p. 9, proof of Theorem 2.6, "Which in turn means that"

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace SubSuperStoch.SuperSpec

theorem eigenvalue_pow_le_normInf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    ∀ μ ∈ SubSuperStoch.SubSpec.specC A, ‖μ‖ ^ m ≤ SubSuperStoch.SubSpec.normInf (A ^ m) := by sorry

end SubSuperStoch.SuperSpec
