-- Prove2me | Theorems.Thm_WassDRCCP_Improved_lemma_1_t_order_statistic
-- name    : WassDRCCP.Improved.lemma_1_t_order_statistic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:26.566571+00:00
-- url     : https://prove2.me/theorems/826ebcbf-7cc9-4816-940e-fd305b047554
-- title:
--   Lemma 1, p. 653 — for x ∈ X_DR(S), t = the (k+1)-th smallest of dist(ξ_i, S(x)) is feasible in (3)
-- statement:
--   Let $\mathcal S(x) = \{\xi : b_p^\top\xi + d_p - a_p^\top x > 0,\ p \in [P]\}$ be the safety set (4a) in a finite-dimensional real normed space, with $P \ge 1$ and every $b_p \ne 0$; let $\xi_1, \dots, \xi_N$ be a sample with $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$, and $k = \lfloor\epsilon N\rfloor$. Fix any $x \in \mathcal X_{\mathrm{DR}}(\mathcal S)$. Then there exist $r \in \mathbb R^N$ and $t \in \mathbb R$ such that $t$ is the $(k+1)$-th smallest value among $\{\operatorname{dist}(\xi_i, \mathcal S(x))\}_{i \in [N]}$ and the constraints of (3) hold:
--   $$t \ge 0,\quad r \ge 0,\quad \operatorname{dist}(\xi_i, \mathcal S(x)) \ge t - r_i\ (i \in [N]),\quad \epsilon t \ge \theta + \frac1N \sum_{i \in [N]} r_i.$$
--
--   The lemma pins the auxiliary variable $t$ of the Wasserstein reformulation to a quantile of the sample distances; this bound on $t$ is what makes the inequality $u_p \ge 0$ of Proposition 1 valid.
--
--   **Formalization Note** The order statistic sorts the $N$ distances with ties counted by multiplicity; $k < N$ follows from $\epsilon < 1$ and $N \ge 1$, so the junk value of an out-of-range rank never occurs. The paper states the lemma for the $\mathcal S$ of §4, the safety set (4). $N \ge 1$, $\epsilon \in (0,1)$, $\theta > 0$ are standing assumptions; $P \ge 1$ and $b_p \ne 0$ make (4) well defined. No big-M constant is involved.
-- source:
--   Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee, Math. Program. 196 (2022) 641–672, p. 653, Lemma 1

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal

namespace WassDRCCP.Improved

/-- Ho-Nguyen, Kılınç-Karzan, Küçükyavuz & Lee (2022), Lemma 1, p. 653: let `k = ⌊ϵN⌋` and
`x ∈ X_DR(S)` for the safety set (4a). Then there is `(r, t)` with `t` equal to the
`(k+1)`-th smallest value among `{dist(ξ_i, S(x))}_{i ∈ [N]}` satisfying the constraints of (3). -/
theorem lemma_1_t_order_statistic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {L N P : ℕ}
    (a : Fin P → Fin L → ℝ) (b : Fin P → StrongDual ℝ E) (d : Fin P → ℝ)
    (ξ : Fin N → E) (X : Set (Fin L → ℝ)) (ϵ θ : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hb : ∀ p, b p ≠ 0)
    (hϵ : 0 < ϵ) (hϵ1 : ϵ < 1) (hθ : 0 < θ) :
    ∀ x ∈ XDR (safetySet a b d) X ξ ϵ θ, ∃ (r : Fin N → ℝ) (t : ℝ),
      t = kthSmallest (fun i => distUnsafe (safetySet a b d x) (ξ i)) (kOf ϵ N) ∧
      0 ≤ t ∧ (∀ i, 0 ≤ r i) ∧
      (∀ i, distUnsafe (safetySet a b d x) (ξ i) ≥ t - r i) ∧
      ϵ * t ≥ θ + (1 / (N : ℝ)) * ∑ i, r i := by sorry

end WassDRCCP.Improved
