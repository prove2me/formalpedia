-- Prove2me | Theorems.Thm_SpectrumLB_lemma_6_6
-- name    : SpectrumLB.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:25.293263+00:00
-- url     : https://prove2.me/theorems/c9f05eb2-cf11-4264-b305-fc0a4d432ff3
-- title:
--   Lemma 6.6 — class decomposition of $d^m\mathcal P_m$ with $A_{m,\mu}=0$ unless $|\mu|\equiv m$, $|\mu|\le m$, and $A_{m,\mu}\le O(n^{\delta(\mu)})$
-- statement:
--   Fix $m\ge0$ and write $d^m\mathcal P_m=\sum_{t=1}^nJ_t^m=\sum_{\pi\in S_n}A_{m,\pi}\,\pi$ in the group algebra $\mathbb Z[S_n]$. Then:
--
--   1. $A_{m,\pi}$ depends only on the conjugacy class $\mu$ of $\pi$, so $d^m\mathcal P_m=A_{m,\varnothing}\mathbf 1+\sum_{\mu\ne\varnothing}A_{m,\mu}K_\mu$ with $K_\mu$ the class sums;
--   2. $A_{m,\mu}=0$ whenever $|\mu|\not\equiv m\pmod 2$ or $|\mu|>m$;
--   3. there is a constant $C_m$ such that for all $n\ge1$ and all $\pi$ of class $\mu$,
--   $$
--   A_{m,\mu}\ \le\ C_m\,n^{\delta(\mu)},\qquad \delta(\mu)=\frac{m+2-|\mu|-2c(\mu)}2;
--   $$
--   4. on $(\mathbb C^d)^{\otimes n}$ the operator identity $d^m\mathcal P_m=\sum_\pi A_{m,\pi}\,\pi$ holds.
--
--   Here $|\mu|$ is the Cayley length and $c(\mu)$ the number of non-trivial cycles. The lemma converts power sums of Jucys–Murphy elements into weighted sums of permutations whose weights are polynomially bounded in $n$.
--
--   Differences from the source:
--   - encoding: coefficients A_{m,μ} of d^m 𝒫_m → coefficients of Σ_t J_t^m in the group algebra ℤ[S_n], with the operator identity as clause 4; reason: for n > d the permutation operators are linearly dependent, so coefficients are defined in the group algebra (paper.md R7)
--   - encoding: class decomposition (6.39) → the coefficient is a class function (clause 1) plus the operator identity (clause 4); reason: equivalent: a class function's expansion is a combination of class sums
--   - encoding: A_{m,μ} ≤ O(n^{δ(μ)}) "otherwise" → ∃ C_m, ∀ n ≥ 1, ∀ π: A ≤ C_m n^{δ} with a real exponent, also for the vanishing coefficients; reason: the constant depends only on m (finitely many classes have |μ| ≤ m); at vanishing coefficients the bound holds for C_m ≥ 0
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 6.6, Eqs. (6.39)–(6.40), pp. 27–28

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_SpectrumLB_jmPowSum
import Definitions.Def_SpectrumLB_jmCoeff
import Definitions.Def_SpectrumLB_cayleyLen
import Definitions.Def_SpectrumLB_ntCycles

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 6.6 (power-sum class decomposition).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 6.6, Eqs. (6.39)–(6.40), pp. 27–28: "Let m ≥ 0 be a constant integer. Then, the mth
Jucys–Murphy power sum admits the following class decomposition. d^m 𝒫_m = A_{m,∅} 1 + Σ_{μ≠∅} A_{m,μ} K_μ,
where the coefficient A_{m,μ} = 0 whenever |μ| ≢ m (mod 2) or |μ| > m; otherwise A_{m,μ} ≤ O(n^{δ(μ)}),
δ(μ) := (m + 2 − |μ| − 2c(μ))/2."

(a) The coefficient of `π` in `Σ_t J_t^m ∈ ℤ[S_n]` is a class function (so the sum is `Σ_μ A_{m,μ} K_μ`);
(b) it vanishes when `|π| ≢ m (mod 2)` or `|π| > m`; (c) it is at most `C_m n^{δ(π)}`; (d) under the
representation on `(ℂ^d)^{⊗n}`, `d^m 𝒫_m = Σ_π A_{m,π} π`.

**Formalization Note.** Coefficients are read in the group algebra (reading R7). In (c) the constant depends
only on `m` (finitely many cycle types have `|μ| ≤ m`); the bound is stated for every `π`, including the
identity (`μ = ∅`) and the vanishing coefficients, with a real exponent. -/
theorem lemma_6_6 (m : ℕ) :
    (∀ n : ℕ, ∀ π σ : Equiv.Perm (Fin n), jmCoeff n m (σ * π * σ⁻¹) = jmCoeff n m π) ∧
    (∀ n : ℕ, ∀ π : Equiv.Perm (Fin n), (cayleyLen π % 2 ≠ m % 2 ∨ m < cayleyLen π) →
      jmCoeff n m π = 0) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ π : Equiv.Perm (Fin n),
      (jmCoeff n m π : ℝ) ≤
        C * (n : ℝ) ^ (((m : ℝ) + 2 - cayleyLen π - 2 * ntCycles π) / 2)) ∧
    (∀ d n : ℕ, (d : ℂ) ^ m • jmPowSum d n m =
      ∑ π : Equiv.Perm (Fin n), (jmCoeff n m π : ℂ) • OptimalSpectrum.Entangled.permOp (ι := Fin d) π) := by sorry

end SpectrumLB
