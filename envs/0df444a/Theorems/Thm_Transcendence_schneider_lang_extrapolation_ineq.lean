-- Prove2me | Theorems.Thm_Transcendence_schneider_lang_extrapolation_ineq
-- name    : Transcendence.schneider_lang_extrapolation_ineq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:54.736759+00:00
-- url     : https://prove2.me/theorems/5b268b48-6fc2-4f44-80f2-80ac1a58586e
-- title:
--   The extrapolation inequality behind (4.19) in the direct proof of Schneider–Lang, uniformly in S₀′ ≥ S₀
-- statement:
--   Let $n \ge 1$ and $d$ be integers, $C \ge 1$, $c_x$ real and $c_F \ge 1$. There is an integer $s_0$ such that for every integer $S_1 \ge s_0$ there is $e_0$ with the following property. Let $T \ge 1$ and $E \ge e_0$ be integers with $\log T \le n\log S_1 + n\log E$, and put $U = S_1ET\log E/(2C\cdot6^{n+1})$ and $N = U/(2C)$. Then for all integers $u \ge ET$ and $M \le 2nu$, with $\rho' = c_FS_1u/T$,
--
--   $$C\bigl(N + M(1 + \log T) + T(S_1 + \log(1 + M))\bigr) + \log M! + \log n + d\log(T+1) + N + T\log\rho' + c_xT\rho' < uS_1\log(u/T).$$
--
--   It is condition 3 of `Transcendence.exists_schneider_lang_parameters`: at the first non-vanishing derivative, of order $M$ with $nu \le M \le 2nu$, it makes the upper bound of the Schwarz step smaller than the lower bound (4.14).
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the inequality of step 6 of §4.6 of Waldschmidt's book (pp. 140–141) that (4.19) is imposed to guarantee, with $S_0' = u$, $E' = u/T$, and $\rho'$ the radius of the polydisc in the Schwarz step. The book gives the asymptotics without proof, and they must hold uniformly in $S_0' \ge S_0$; here they hold for every $u \ge ET$. It is real arithmetic. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6, step 6 and (4.19) (pp. 140–141). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **The extrapolation inequality (4.19) of the proof of Schneider–Lang, uniformly** (Waldschmidt, *Diophantine
Approximation on Linear Algebraic Groups*, §4.6; the book does not spell out the uniformity). Let `n ≥ 1`, `d`,
`C ≥ 1`, `cx` and `cF ≥ 1`. For every large enough `S₁` there is `e₀` such that, whenever `T ≥ 1`, `E ≥ e₀`,
`log T ≤ n log S₁ + n log E`, `U = S₁ E T log E / (2C·6^{n+1})` and `N = U/(2C)`, for all integers `u ≥ E T` and
`M ≤ 2nu`, with `ρ' = cF S₁ u / T`:
`C (N + M (1 + log T) + T (S₁ + log (1 + M))) + log M! + log n + d log (T + 1) + N + T log ρ' + cx T ρ'
  < u S₁ log (u/T)`. -/
theorem schneider_lang_extrapolation_ineq (n d : ℕ) (C cx cF : ℝ) (hn : 1 ≤ n) (hC : 1 ≤ C)
    (hcF : 1 ≤ cF) :
    ∃ s₀ : ℕ, ∀ S₁ : ℕ, s₀ ≤ S₁ → ∃ e₀ : ℝ, ∀ (T E : ℕ) (U N : ℝ), 1 ≤ T → e₀ ≤ E →
      Real.log T ≤ n * Real.log S₁ + n * Real.log E →
      U = S₁ * (E * T) * Real.log E / (2 * C * 6 ^ (n + 1)) → N = U / (2 * C) →
      ∀ u M : ℕ, E * T ≤ u → M ≤ 2 * n * u →
        C * (N + M * (1 + Real.log T) + T * (S₁ + Real.log (1 + M))) +
          Real.log (M.factorial : ℝ) + Real.log n +
          (d * Real.log (T + 1) + N + T * Real.log (cF * S₁ * u / T) +
            cx * T * (cF * S₁ * u / T)) < u * S₁ * Real.log (u / T) := by
  sorry

end Transcendence
