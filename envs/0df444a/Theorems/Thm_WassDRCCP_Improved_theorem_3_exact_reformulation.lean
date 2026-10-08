-- Prove2me | Theorems.Thm_WassDRCCP_Improved_theorem_3_exact_reformulation
-- name    : WassDRCCP.Improved.theorem_3_exact_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:38.408624+00:00
-- url     : https://prove2.me/theorems/9ebf553d-53e7-4ff6-9123-f8a20fc84c95
-- title:
--   Theorem 3, p. 655 — the reduced quantile-strengthened MIP (20) is an exact reformulation of (DR-CCP): X_DR(S) = {x ∈ X : (20b)–(20d)}
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and dual norm $\|\cdot\|_*$. Let $\xi_1, \dots, \xi_N \in E$ be a sample with $N \ge 1$, $\epsilon \in (0,1)$ a risk tolerance and $\theta > 0$ a Wasserstein radius. For $p \in [P]$, $P \ge 1$, let $a_p \in \mathbb R^L$, $d_p \in \mathbb R$ and $b_p$ a nonzero continuous linear functional on $E$, and let
--   $$\mathcal S(x) = \{\xi : b_p^\top\xi + d_p - a_p^\top x > 0,\ p \in [P]\}$$
--   be the safety set of a joint chance constraint with right-hand side uncertainty. Let $\mathcal X \subseteq \mathbb R^L$ and let $M$ satisfy $|b_p^\top\xi_i + d_p - a_p^\top x|/\|b_p\|_* \le M$ for all $x \in \mathcal X$, $i \in [N]$, $p \in [P]$. Put $k = \lfloor\epsilon N\rfloor$, let $q_p$ be the $(k+1)$-th largest value among $\{-b_p^\top\xi_i\}_{i\in[N]}$, and $[N]_p = \{i \in [N] : -b_p^\top\xi_i > q_p\}$. Then
--   $$\mathcal X_{\mathrm{DR}}(\mathcal S) = \{x \in \mathcal X : \exists\,(z, r, t) \text{ satisfying (20b)–(20d)}\},$$
--   where $\mathcal X_{\mathrm{DR}}(\mathcal S)$ is the set of $x \in \mathcal X$ with $\sup_{\mathbb P \in \mathcal F_N(\theta)} \mathbb P[\xi \notin \mathcal S(x)] \le \epsilon$ over the 1-Wasserstein ball $\mathcal F_N(\theta)$ around the empirical distribution, and the constraints are:
--   1. (20b): $z \in \{0,1\}^N$, $t \ge 0$, $r \ge 0$, $x \in \mathcal X$ (5b); $\epsilon t \ge \theta + \frac1N\sum_i r_i$ (5c); $M(1 - z_i) \ge t - r_i$ for $i \in [N]$ (5d); $\sum_i z_i \le \lfloor\epsilon N\rfloor$ (8c);
--   2. (20c): $\dfrac{b_p^\top\xi_i + d_p - a_p^\top x}{\|b_p\|_*} + \dfrac{-b_p^\top\xi_i - q_p}{\|b_p\|_*} z_i \ge t - r_i$ only for $i \in [N]_p$, $p \in [P]$;
--   3. (20d): $\dfrac{-q_p + d_p - a_p^\top x}{\|b_p\|_*} \ge t$ for $p \in [P]$.
--
--   This is the paper's main reformulation: of the $NP$ inequalities (17c), only those with $i \in [N]_p$ — at most $\lfloor\epsilon N\rfloor$ per row — are kept, and the big-M coefficients of (5e) are replaced by data-driven ones, without changing the feasible set of the distributionally robust chance-constrained program.
--
--   **Formalization Note** "Exact reformulation" is stated as equality of the sets of feasible $x$, as (9) does for Theorem 1; since the objective $c^\top x$ depends on $x$ alone, the optimal value and optimal $x$ coincide. The norm on $E$ is arbitrary and $\|b_p\|_*$ is the operator norm of $b_p$. The paper's "sufficiently large" $M$ (needed in (5d)) is pinned by Remark 1, (10), as one bound uniform in $i$, and compactness of $\mathcal X$ is replaced by the existence of that bound. $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$ are the standing assumptions of §§2–4; $P \ge 1$ and $b_p \ne 0$ make (4) well defined. The binaries are real numbers with $z_i \in \{0,1\}$; ties in $q_p$ are counted with multiplicity, so $[N]_p$ has at most $k$ elements.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 655, Theorem 3, (20)

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), Theorem 3, p. 655: formulation (20) is an
exact reformulation of (DR-CCP) for the safety set (4a), i.e.
`X_DR(S) = {x ∈ X : (20b)–(20d)}`: (5b)–(5d), (8c), the inequality (20c) only for
`i ∈ [N]_p`, and (20d). -/
theorem theorem_3_exact_reformulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ M : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ)
    (hM : ∀ x ∈ X, ∀ (i : Fin N) (p : Fin P), |b p (ξ i) + d p - a p ⬝ᵥ x| / ‖b p‖ ≤ M) :
    XDR (safetySet a b d) X ξ ϵ θ =
      {x | x ∈ X ∧ ∃ (z r : Fin N → ℝ) (t : ℝ), sys20 a b d ξ X ϵ θ M x z r t} := by sorry

end WassDRCCP.Improved
