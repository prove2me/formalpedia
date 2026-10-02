-- Prove2me | Theorems.Thm_Transcendence_exists_schneider_lang_parameters
-- name    : Transcendence.exists_schneider_lang_parameters
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:04.546215+00:00
-- url     : https://prove2.me/theorems/483ae7ac-c47e-455f-9cdd-bcd2d8128133
-- title:
--   Parameters for the direct proof of the criterion of Schneider–Lang: the hypotheses of Proposition 4.10 and the inequalities behind (4.17) and (4.19)
-- statement:
--   Let $1 \le n < d$ be integers, $C \ge 1$, $c_x, c_y \ge 0$ and $c_F \ge 1$. There are integers $S_1, T, E \ge 1$ and real numbers $U, N > 0$ such that, with $r = (c_y + 2)S_1$ and $R = Er$:
--
--   1. $12n^2 \le N + 2U$, $e \le E \le e^{(N + 2U)/6}$, $(T+1)^{d}R^{T}e^{c_xTR} \le e^{U}$ and $\bigl(2(N + 2U)\bigr)^{n+1} \le (T+1)^{d}N(\log E)^{n}$;
--   2. for every integer $k < nET$,
--   $$C\bigl(N + k(1 + \log T) + T(S_1 + \log(1 + k))\bigr) + \log k! < U;$$
--   3. for all integers $u \ge ET$ and $M \le 2nu$, with $\rho' = c_FS_1u/T$,
--   $$C\bigl(N + M(1 + \log T) + T(S_1 + \log(1 + M))\bigr) + \log M! + \log n + d\log(T+1) + N + T\log\rho' + c_xT\rho' < uS_1\log(u/T).$$
--
--   In the proof of `Transcendence.schneider_lang_cartesian`, $C$ is the constant of (4.14) and $c_F$ that of the Schwarz step: condition 1 gives the auxiliary function (`Transcendence.exists_exp_monomials_small_on_grid`), condition 2 makes its derivatives of order less than $nET$ vanish at the grid points, and condition 3 rules out a first non-vanishing one.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the choice of parameters at the end of §4.6 of Waldschmidt's book (p. 141), in its shape: $S_1$ is fixed and large, then $T = (S_1m)^n$, an $n$-th power and a multiple of $S_1^n$ as the book asks, and $E = S_1^{d-1-n}m^{d-n}$, for a large integer $m$; $U = S_1ET\log E/(2C\cdot6^{n+1})$ and $N = U/(2C)$. The role of the book's $S_0$ is played by $ET$, and $ET\cdot S_1 = T^{d/n}$. Conditions 2 and 3 are the inequalities that the book's (4.17) and (4.19) are imposed to guarantee. The book gives their asymptotics without proof; they are proved in `Transcendence.schneider_lang_vanishing_ineq` and `Transcendence.schneider_lang_extrapolation_ineq`, the second uniformly in $S_0' = u \ge ET$. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6: the conditions (4.15)–(4.19) and the choice of parameters in step 6 (pp. 138–141). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **The parameters of the proof of Schneider–Lang** (Waldschmidt, *Diophantine Approximation on Linear
Algebraic Groups*, §4.6, conditions (4.15)–(4.19)). Let `1 ≤ n < d`, `C ≥ 1`, `cx, cy ≥ 0` and `cF ≥ 1`. There
are integers `S₁, T, E ≥ 1` and reals `U, N > 0` such that
* the hypotheses of Prop. 4.10 hold for `n`, `L = (T+1)^d` and the radii `r = (cy + 2) S₁`, `R = E r`:
  `12n² ≤ N + 2U`, `e ≤ E ≤ e^{(N + 2U)/6}`, `(T+1)^d R^T e^{cx T R} ≤ e^U` and
  `(2(N + 2U))^{n+1} ≤ (T+1)^d N (log E)ⁿ`;
* (4.17) `C (N + k (1 + log T) + T (S₁ + log (1 + k))) + log k! < U` for every `k < n E T`;
* (4.19) `C (N + M (1 + log T) + T (S₁ + log (1 + M))) + log M! + log n + d log (T + 1) + N + T log ρ' +
  cx T ρ' < u S₁ log (u/T)`, where `ρ' = cF S₁ u / T`, for all integers `u ≥ E T` and `M ≤ 2nu`. -/
theorem exists_schneider_lang_parameters (n d : ℕ) (C cx cy cF : ℝ) (hn : 1 ≤ n)
    (hd : n + 1 ≤ d) (hC : 1 ≤ C) (hcx : 0 ≤ cx) (hcy : 0 ≤ cy) (hcF : 1 ≤ cF) :
    ∃ (S₁ T E : ℕ) (U N : ℝ), 1 ≤ S₁ ∧ 1 ≤ T ∧ 1 ≤ E ∧ 0 < U ∧ 0 < N ∧
      (12 * (n : ℝ) ^ 2 ≤ N + U + U ∧ Real.exp 1 ≤ (E : ℝ) ∧
        (E : ℝ) ≤ Real.exp ((N + U + U) / 6) ∧
        ((T : ℝ) + 1) ^ d * ((E : ℝ) * ((cy + 2) * S₁)) ^ T *
          Real.exp (cx * T * ((E : ℝ) * ((cy + 2) * S₁))) ≤ Real.exp U ∧
        (2 * (N + U + U)) ^ (n + 1) ≤ ((T : ℝ) + 1) ^ d * N * Real.log (E : ℝ) ^ n) ∧
      (∀ k : ℕ, k < n * (E * T) →
        C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k))) +
          Real.log (k.factorial : ℝ) < U) ∧
      ∀ u M : ℕ, E * T ≤ u → M ≤ 2 * n * u →
        C * (N + M * (1 + Real.log T) + T * (S₁ + Real.log (1 + M))) +
          Real.log (M.factorial : ℝ) + Real.log n +
          (d * Real.log (T + 1) + N + T * Real.log (cF * S₁ * u / T) +
            cx * T * (cF * S₁ * u / T)) < u * S₁ * Real.log (u / T) := by
  sorry

end Transcendence
