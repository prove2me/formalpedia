-- Prove2me | Theorems.Thm_WassDRCCP_Improved_theorem_2_exact_reformulation
-- name    : WassDRCCP.Improved.theorem_2_exact_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:30.234161+00:00
-- url     : https://prove2.me/theorems/edfe2d7c-db6e-40a9-a176-0d5ed255a140
-- title:
--   Theorem 2, p. 651 — formulation (17) with quantile-strengthened coefficients is an exact reformulation of (DR-CCP)
-- statement:
--   In the setting of (6) (safety set (4a), $P \ge 1$, $b_p \ne 0$, $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$, and $M$ bounding $|b_p^\top\xi_i + d_p - a_p^\top x|/\|b_p\|_*$ over $\mathcal X$), let $k = \lfloor\epsilon N\rfloor$ and let $q_p$ be the $(k+1)$-th largest value among $\{-b_p^\top\xi_i\}_{i \in [N]}$. Then
--   $$\mathcal X_{\mathrm{DR}}(\mathcal S) = \{x \in \mathcal X : \exists\,(z, r, t) \text{ satisfying (17b)–(17c)}\},$$
--   where (17b) consists of (5b), (5c), (5d) and the cardinality constraint (8c) $\sum_i z_i \le k$, and (17c) is
--   $$\frac{b_p^\top\xi_i + d_p - a_p^\top x}{\|b_p\|_*} + \frac{-b_p^\top\xi_i - q_p}{\|b_p\|_*}\, z_i \ge t - r_i, \qquad i \in [N],\ p \in [P].$$
--
--   The big-M coefficient of (5e) is replaced by the data-driven coefficient $(-b_p^\top\xi_i - q_p)/\|b_p\|_*$, which is typically much smaller; the theorem says this does not change the feasible set.
--
--   **Formalization Note** The paper prints (17b) as "(5b)–(5d) and (5c)", repeating (5c), which (5b)–(5d) already contains. It is read as (8c): the proof begins "By Theorem 1, (5) with (8c) is an exact reformulation", (20b) of the same section has (8c), and Proposition 1 must deliver (8c) for Theorem 3. The equality holds under either reading. The constant $M$ still appears through (5d) and is pinned as in (6). Ties among the $-b_p^\top\xi_i$ are counted with multiplicity. Feasible-set equality is the reading of "exact reformulation", as in (9).
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 651, Theorem 2, (17)

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), Theorem 2, p. 651: formulation (17) is an
exact reformulation of (DR-CCP) for the safety set (4a), i.e.
`X_DR(S) = {x ∈ X : (17b)–(17c)}`, where (17b) is (5b)–(5d) together with the cardinality
constraint (8c). -/
theorem theorem_2_exact_reformulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hM : ∀ x ∈ X, ∀ (i : Fin N) (p : Fin P), |b p (ξ i) + d p - a p ⬝ᵥ x| / ‖b p‖ ≤ M) :
    XDR (safetySet a b d) X ξ ϵ θ =
      {x | x ∈ X ∧ ∃ (z r : Fin N → ℝ) (t : ℝ), sys17 a b d ξ X ϵ θ M x z r t} := by sorry

end WassDRCCP.Improved
