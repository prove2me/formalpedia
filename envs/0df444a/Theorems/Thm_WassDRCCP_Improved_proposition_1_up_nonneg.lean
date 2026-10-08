-- Prove2me | Theorems.Thm_WassDRCCP_Improved_proposition_1_up_nonneg
-- name    : WassDRCCP.Improved.proposition_1_up_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:26.9157+00:00
-- url     : https://prove2.me/theorems/57e823b5-82a0-487d-a3e0-cd45314e0013
-- title:
--   Proposition 1, p. 654 — for x ∈ X_DR(S) some (r, t, z) satisfies (17b)–(17c) with u_p = g*_p(x) − t ≥ 0 for every p
-- statement:
--   In the setting of Theorem 2 (safety set (4a), $P \ge 1$, $b_p \ne 0$, $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$, and $M$ bounding $|b_p^\top\xi_i + d_p - a_p^\top x|/\|b_p\|_*$ over $\mathcal X$), let $k = \lfloor\epsilon N\rfloor$ and $q_p$ the $(k+1)$-th largest value among $\{-b_p^\top\xi_i\}_{i\in[N]}$. For every $x \in \mathcal X_{\mathrm{DR}}(\mathcal S)$ there exists $(r, t, z)$ such that $(x, r, t, z)$ satisfies (17b)–(17c) and, for every $p \in [P]$,
--   $$u_p = \frac{-q_p + d_p - a_p^\top x}{\|b_p\|_*} - t \ge 0.$$
--
--   The proposition shows that the inequality $u_p \ge 0$ can be imposed without cutting off any $x$; once it is imposed, the rows of (17c) with nonpositive coefficient $h_{i,p}$ become redundant, which yields the reduced formulation (20).
--
--   **Formalization Note** (17b) contains (5b), (5c), (5d) and (8c) (see Theorem 2 for the reading of the printed "(5c)"); because (5d) involves $M$, the big-M bound of (6) is assumed. The witness is only asserted to exist; the paper's proof takes $t$ from Lemma 1. Ties are counted with multiplicity in $q_p$.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 654, Proposition 1

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), Proposition 1, p. 654: suppose `θ > 0`.
For every `x ∈ X_DR(S)` (safety set (4a)) there is `(r, t, z)` such that `(x, r, t, z)` satisfies
(17b)–(17c) and, for every `p ∈ [P]`, `u_p = (−q_p + d_p − a_p^⊤x)/‖b_p‖_* − t ≥ 0`. -/
theorem proposition_1_up_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hM : ∀ x ∈ X, ∀ (i : Fin N) (p : Fin P), |b p (ξ i) + d p - a p ⬝ᵥ x| / ‖b p‖ ≤ M) :
    ∀ x ∈ XDR (safetySet a b d) X ξ ϵ θ, ∃ (z r : Fin N → ℝ) (t : ℝ),
      sys17 a b d ξ X ϵ θ M x z r t ∧ ∀ p, gstar a b d ξ (kOf ϵ N) x p - t ≥ 0 := by sorry

end WassDRCCP.Improved
