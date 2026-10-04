-- Prove2me | Theorems.Thm_TeschlODE_Horseshoe_symDistZ_agree
-- name    : TeschlODE.Horseshoe.symDistZ_agree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:03:28.926153+00:00
-- url     : https://prove2.me/theorems/c5a32a60-6b3f-4a62-a2de-560688b5942e
-- title:
--   Lemma 11.15 (corrected) — on the two-sided $\Sigma_N$, agreement on $|j| \le n$ versus $d(x,y)$ compared with $N^{-n}$
-- statement:
--   Let $N \ge 2$ and equip $\Sigma_N = \{0, \dots, N-1\}^{\mathbb{Z}}$ with the metric (11.35),
--   $d(x,y) = \tfrac12 \sum_{n \ge 0} (|x_n - y_n| + |x_{-n} - y_{-n}|)/N^n$. Then for every $n \in \mathbb{N}_0$:
--   $$x_j = y_j \text{ for all } |j| \le n \implies d(x, y) \le N^{-n},$$
--   $$x_j \ne y_j \text{ for some } |j| \le n \implies d(x, y) \ge \tfrac12 N^{-n}.$$
--   The lemma says that two-sided sequences are close exactly when they agree on a long central block. This is what makes the itinerary map of the horseshoe continuous with a continuous inverse.
--
--   **Formalization Note.** *Correction to the page.* The book prints $d(x,y) \ge N^{-n}$ in the second clause. That is false for the metric (11.35): for $N = 2$, $n = 1$ and $x, y$ differing only at $j = 1$, $d(x,y) = \tfrac12 \cdot \tfrac12 = \tfrac14 < \tfrac12$. The factor $\tfrac12$ in (11.35) halves the contribution of every index $j \ne 0$, so the correct lower bound is $\tfrac12 N^{-n}$, and that bound is attained. The first clause is stated as printed. $N \in \mathbb{N} \setminus \{1\}$ is read as $N \ge 2$ ($N = 0$ gives an empty alphabet).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 306, Lemma 11.15

import Mathlib
import Definitions.Def_TeschlODE_Horseshoe_symDistZ

namespace TeschlODE.Horseshoe

/-- Teschl, Lemma 11.15, p. 306, **corrected**: on the two-sided space `Σ_N = {0, …, N − 1}^ℤ`
(`N ∈ ℕ \ {1}`, so `N ≥ 2`) with the metric (11.35), `d(x, y) ≤ N⁻ⁿ` if `xⱼ = yⱼ` for all
`|j| ≤ n`, and `d(x, y) ≥ N⁻ⁿ / 2` if `xⱼ ≠ yⱼ` for at least one `|j| ≤ n`.
The book prints `d(x, y) ≥ N⁻ⁿ` in the second clause, which is false for (11.35): for `N = 2`,
`n = 1` and `x, y` differing only at `j = 1`, `d(x, y) = 1/4 < 1/2`. The factor `1/2` of (11.35)
halves the contribution of an index `j ≠ 0`; the corrected bound `N⁻ⁿ / 2` is attained. -/
theorem symDistZ_agree (N : ℕ) (hN : 2 ≤ N) (x y : ℤ → Fin N) (n : ℕ) :
    ((∀ j : ℤ, |j| ≤ n → x j = y j) → symDistZ N x y ≤ 1 / (N : ℝ) ^ n) ∧
      ((∃ j : ℤ, |j| ≤ n ∧ x j ≠ y j) → 1 / (2 * (N : ℝ) ^ n) ≤ symDistZ N x y) := by sorry

end TeschlODE.Horseshoe
