-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_68
-- name    : QRepeaterBench.Dephasing.eq_68
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:37.107224+00:00
-- url     : https://prove2.me/theorems/9d6912ee-fbde-40fd-afd4-e4ebd4ce5b23
-- title:
--   Eq. (68) — S(ρ‖σ) = −S(ρ) − Σ_i ⟨i|ρ|i⟩ log s_i in the eigenbasis {|i⟩, s_i} of σ (support of ρ inside that of σ)
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices on a finite-dimensional Hilbert space, and write $\sigma=\sum_i s_i|i\rangle\langle i|$ in an orthonormal eigenbasis $\{|i\rangle\}$ with eigenvalues $s_i$, i.e. $\sigma=UDU^\dagger$ with $U$ unitary (its columns are the $|i\rangle$) and $D=\mathrm{diag}(s_i)$. Assume that the support of $\rho$ lies in the support of $\sigma$: $\langle i|\rho|i\rangle=0$ whenever $s_i=0$. Then the relative entropy (in bits) is
--
--   $$S(\rho\|\sigma)=-S(\rho)-\mathrm{Tr}(\rho\log\sigma)=-S(\rho)-\sum_i\langle i|\rho|i\rangle\log s_i ,$$
--
--   where the terms with $s_i=0$ vanish.
--
--   This is the computational formula the paper uses for every relative entropy against a candidate separable state; for the dephasing channel it is applied with $\sigma=\tilde\sigma$.
--
--   **Formalization Note** The relative entropy is the published `relativeEntropyBits` (Umegaki entropy divided by $\ln 2$, $+\infty$ off support), and logarithms are base 2, in line with the paper's REE in bits. The support hypothesis is implicit on the page: without it the left side is $+\infty$. The right side is wrapped in `ENNReal.ofReal`; it is nonnegative under the hypotheses.
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 10, Eq. (68)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_68 {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (hσ : QAlgorithms.IsDensityMatrix σ) (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (s : ι → ℝ) (hσU : σ = U * Matrix.diagonal (fun i => (s i : ℂ)) * Uᴴ) (hsupp : ∀ i, s i = 0 → (Uᴴ * ρ * U) i i = 0) : QAlgorithms.Papers.Independent.Information100.P54.relativeEntropyBits ρ σ = ENNReal.ofReal (-QAlgorithms.vnEntropy ρ - ∑ i, ((Uᴴ * ρ * U) i i).re * Real.logb 2 (s i)) := by sorry
end QRepeaterBench.Dephasing
