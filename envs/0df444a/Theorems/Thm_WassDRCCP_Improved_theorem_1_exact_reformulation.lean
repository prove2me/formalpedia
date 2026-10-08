-- Prove2me | Theorems.Thm_WassDRCCP_Improved_theorem_1_exact_reformulation
-- name    : WassDRCCP.Improved.theorem_1_exact_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:22.866099+00:00
-- url     : https://prove2.me/theorems/2bf6cbf2-f4de-4d91-be56-38caf9ff4ce2
-- title:
--   Theorem 1, p. 648 — formulation (8) is an exact reformulation of (DR-CCP): X_DR(S) = {x ∈ X : (8b)–(8d)}
-- statement:
--   In the setting of (6) — the safety set $\mathcal S(x) = \{\xi : b_p^\top\xi + d_p - a_p^\top x > 0,\ p\in[P]\}$ in a finite-dimensional real normed space, $P \ge 1$, $b_p \ne 0$, a sample of size $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$, and a constant $M$ bounding $|b_p^\top\xi_i + d_p - a_p^\top x|/\|b_p\|_*$ over $x \in \mathcal X$, $i \in [N]$, $p \in [P]$ — one has
--   $$\mathcal X_{\mathrm{DR}}(\mathcal S) = \{x \in \mathcal X : \exists\,(z, r, t) \text{ satisfying (8b)–(8d)}\},$$
--   where (8b) is (5b)–(5e), (8c) is the cardinality constraint $\sum_{i \in [N]} z_i \le \lfloor \epsilon N \rfloor$, and (8d) is $\frac{b_p^\top\xi_i + d_p - a_p^\top x}{\|b_p\|_*} + M z_i \ge 0$ for $i \in [N]$, $p \in [P]$.
--
--   The point of the theorem is that the same binary variables $z$ of the big-M formulation (5) can carry the knapsack and big-M constraints of the sample average approximation, so the strengthening adds no new binaries. Its proof uses $\theta > 0$.
--
--   **Formalization Note** "Exact reformulation" is stated as equality of the sets of feasible $x$, the form (9) prints; since the objective $c^\top x$ depends on $x$ alone, this gives the same optimal value and optimal $x$. $M$ is pinned as in (6) (Remark 1, (10), uniform in $i$); $\mathcal X$ is not assumed compact. $\lfloor\epsilon N\rfloor$ is `Nat.floor`.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 648, Theorem 1, (9)

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), Theorem 1, p. 648, (9): for the safety
set (4a), `X_DR(S) = {x ∈ X : (8b)–(8d)}`, with the big-M constant `M` of Remark 1, (10). -/
theorem theorem_1_exact_reformulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hM : ∀ x ∈ X, ∀ (i : Fin N) (p : Fin P), |b p (ξ i) + d p - a p ⬝ᵥ x| / ‖b p‖ ≤ M) :
    XDR (safetySet a b d) X ξ ϵ θ =
      {x | x ∈ X ∧ ∃ (z r : Fin N → ℝ) (t : ℝ), sys8 a b d ξ X ϵ θ M x z r t} := by sorry

end WassDRCCP.Improved
