-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_C_3_exact_socp
-- name    : SpectralFeedback.Supplement.theorem_C_3_exact_socp
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:56:31.205469+00:00
-- url     : https://prove2.me/theorems/70a0420c-4b43-4eb1-ba0c-932d5c8616af
-- title:
--   Theorem C.3 — $G_{m,r}(\rho)$ equals the optimum of an explicit hive and rotated-cone program
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^d$, $n=\operatorname{rank}\rho$, $\lambda=(\lambda_1(\rho),\dots,\lambda_n(\rho))$ its positive spectrum, $m,r\ge1$ and $r'=\min\{r,n\}$. Consider the finite program: choose a decreasing nonnegative $x\in\mathbb R^n$ of trace $1/m$, partial-sum spectra $s^h$ (all decreasing and nonnegative) and real hives with
--
--   $$
--   s^1=x,\qquad s^m=\lambda,\qquad H_n(s^{h-1},x;s^h)\quad(2\le h\le m),\qquad\text{(C.10)}
--   $$
--
--   and maximize $mz$ subject also to the rotated-cone constraints (C.8) for $x_1,\dots,x_{r'}$:
--
--   $$
--   z\ge0,\quad u_i\ge0,\quad z^2\le u_i(x_i+z)\ (1\le i\le r'),\quad \sum_iu_i\le(r'-1)z .
--   $$
--
--   For $m=1$, $x=\lambda$ and there are no hives. Then the value
--
--   $$
--   G_{m,r}(\rho)=\max_{A_h\succeq0,\ \sum_hA_h=\rho}\ \sum_{h=1}^m\chi\bigl(\lambda_1(A_h),\dots,\lambda_r(A_h)\bigr)
--   $$
--
--   exists, the program's optimum is attained, and the two are equal. The program has $O(mn^2)$ scalar variables and linear constraints and $r'$ three-dimensional rotated cones.
--
--   The theorem turns the matrix optimization defining $G_{m,r}$ into a finite second-order cone program in the spectrum of $\rho$ alone.
--
--   Differences from the source:
--   - generalization: receiver rank r with r ≤ k ≤ d (Theorem C.1) → any r ≥ 1; reason: f_r pads eigenvalues with zeros and r′ = min{r, n} is unchanged, so r > d adds no new case; for r ≤ d it is the source's statement
--   - encoding: the value G_{m,r}(ρ) (a maximum, (C.6)) → IsGreatest of the published rewardSet with F = χ_r; reason: the base mission's convention; IsGreatest asserts the maximum exists and equals the value, never a junk sSup
--   - encoding: the optimum of the program → IsGreatest of socpValues (the set of feasible objective values m z); reason: asserts the optimum is attained and equals the value
--   - encoding: hive labels H_{ij} on i + j ≤ n → a function ℕ → ℕ → ℝ constrained on the triangle only; reason: values off the triangle occur in no constraint
--   - reading: the formulation uses O(mn²) scalar variables and linear constraints and r′ three-dimensional rotated cones → not a separate conjunct; realized by the program's explicit variables (m − 1 hives on the labels i + j ≤ n, r′ cones); reason: the sentence describes the displayed program, which socpValues writes out exactly; an asymptotic count has no constant to state
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem C.3, p.28 (PDF p.30); notation §C.3, p.27 (PDF p.29); hives (C.9), §C.15.1

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi
import Definitions.Def_SpectralFeedback_Supplement_socpValues

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem C.3** (An exact polynomial-size SOCP; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.28 (PDF p.30)). With the
notation of §C.3 (p.27: `n = rank ρ`, `r′ = min{r, n}`, `λ = (λ_1(ρ), …, λ_n(ρ))`), the value
`G_{m,r}(ρ)` equals the optimum of the finite program: choose a decreasing nonnegative `x ∈ ℝ^n` of
trace `1/m`, partial-sum spectra `s^h` and real hives with `s^1 = x`, `s^m = λ`,
`H_n(s^{h−1}, x; s^h)` (`2 ≤ h ≤ m`) (C.10); maximize `m z` subject also to (C.8) for
`x_1, …, x_{r′}`. All partial spectra are decreasing and nonnegative. For `m = 1`, `x = λ` and there
are no hives.

**Formalization Note** `ρ` is a density matrix (positive semidefinite, trace one), the standing
assumption of §C.3. Both maxima are `IsGreatest`: the conclusion is that `G_{m,r}(ρ)` exists, the
program's optimum is attained, and the two are equal. The program is `socpValues` (definition
`SpectralFeedback.Supplement.socpValues`), whose variables are exactly the displayed ones (`m − 1`
hives on the labels `i + j ≤ n`, `r′` rotated cones); the sentence on its size (`O(mn²)` variables and
linear constraints, `r′` cones) is a description of this structure and is not a separate conjunct.
The case `m = 1` is covered uniformly (then `S 0 = x = λ` and no hive constraint applies). -/
theorem theorem_C_3_exact_socp (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ v : ℝ, IsGreatest (rewardSet r (chi r) m ρ) v ∧
      IsGreatest (socpValues ρ.rank m r (fun i => eigDesc ρ (i : ℕ))) v := by sorry

end Supplement

end SpectralFeedback
