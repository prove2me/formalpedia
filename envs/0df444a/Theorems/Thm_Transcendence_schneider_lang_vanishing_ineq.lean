-- Prove2me | Theorems.Thm_Transcendence_schneider_lang_vanishing_ineq
-- name    : Transcendence.schneider_lang_vanishing_ineq
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:08.697987+00:00
-- url     : https://prove2.me/theorems/36ba44ee-12ee-466a-9ed0-d6d75c56e741
-- title:
--   The vanishing inequality behind (4.17) in the direct proof of Schneider–Lang holds for S₁ large, then E large
-- statement:
--   Let $n \ge 1$ be an integer and $C \ge 1$. There is an integer $s_0$ such that for every integer $S_1 \ge s_0$ there is $e_0$ with the following property. Let $T \ge 1$ and $E \ge e_0$ be integers with $\log T \le n\log S_1 + n\log E$, and put
--
--   $$U = \frac{S_1ET\log E}{2C\cdot6^{n+1}}, \qquad N = \frac{U}{2C}.$$
--
--   Then for every integer $k < nET$,
--
--   $$C\bigl(N + k(1 + \log T) + T(S_1 + \log(1 + k))\bigr) + \log k! < U.$$
--
--   It is condition 2 of `Transcendence.exists_schneider_lang_parameters`: set against (4.14) and (4.16), it makes every derivative of order less than $nET$ of the auxiliary function vanish at the grid points.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the inequality of step 4 of §4.6 of Waldschmidt's book (p. 139) that (4.17) is imposed to guarantee, for derivatives of total order $k < nS_0$ with $S_0 = ET$, and for the parameters of `Transcendence.exists_schneider_lang_parameters`. It is real arithmetic. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6, step 4 and (4.17) (p. 139). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **The vanishing inequality (4.17) of the proof of Schneider–Lang** (Waldschmidt, *Diophantine Approximation
on Linear Algebraic Groups*, §4.6). Let `n ≥ 1` and `C ≥ 1`. For every large enough `S₁` there is `e₀` such that,
whenever `T ≥ 1`, `E ≥ e₀`, `log T ≤ n log S₁ + n log E`, `U = S₁ E T log E / (2C·6^{n+1})` and `N = U/(2C)`,
`C (N + k (1 + log T) + T (S₁ + log (1 + k))) + log k! < U` for every `k < n E T`. -/
theorem schneider_lang_vanishing_ineq (n : ℕ) (C : ℝ) (hn : 1 ≤ n) (hC : 1 ≤ C) :
    ∃ s₀ : ℕ, ∀ S₁ : ℕ, s₀ ≤ S₁ → ∃ e₀ : ℝ, ∀ (T E : ℕ) (U N : ℝ), 1 ≤ T → e₀ ≤ E →
      Real.log T ≤ n * Real.log S₁ + n * Real.log E →
      U = S₁ * (E * T) * Real.log E / (2 * C * 6 ^ (n + 1)) → N = U / (2 * C) →
      ∀ k : ℕ, k < n * (E * T) →
        C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k))) +
          Real.log (k.factorial : ℝ) < U := by
  sorry

end Transcendence
