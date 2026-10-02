-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_symDist_agree
-- name    : TeschlODE.IntervalMaps.symDist_agree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T18:48:51.142634+00:00
-- url     : https://prove2.me/theorems/a10058ab-eb25-4614-84ee-4662beb147c2
-- title:
--   Lemma 11.6 — on Σ_N, agreement of the first n+1 symbols versus d(x,y) compared with N^{-n}
-- statement:
--   Let $N \ge 2$ and let $d$ be the metric (11.28) on $\Sigma_N$. For $x, y \in \Sigma_N$ and $n \in \mathbb{N}_0$:
--   $$x_j = y_j \ \ \forall j \le n \;\Longrightarrow\; d(x,y) \le N^{-n}, \qquad x_j \ne y_j \text{ for some } j \le n \;\Longrightarrow\; d(x,y) \ge N^{-n}.$$
--   So two sequences are close exactly when a long initial block of them agrees.
--
--   **Formalization Note.** The book's $N \in \mathbb{N} \setminus \{1\}$ is the hypothesis $2 \le N$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 302, Lemma 11.6

import Mathlib
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.6, p. 302: on `Σ_N` (`N ∈ ℕ \ {1}`, so `N ≥ 2`) with the metric (11.28),
`d(x, y) ≤ N⁻ⁿ` if `xⱼ = yⱼ` for all `j ≤ n`, and `d(x, y) ≥ N⁻ⁿ` if `xⱼ ≠ yⱼ` for at least one
`j ≤ n`. -/
theorem symDist_agree (N : ℕ) (hN : 2 ≤ N) (x y : ℕ → Fin N) (n : ℕ) :
    ((∀ j, j ≤ n → x j = y j) → TeschlODE.Shared.symDist N x y ≤ 1 / (N : ℝ) ^ n) ∧
      ((∃ j, j ≤ n ∧ x j ≠ y j) → 1 / (N : ℝ) ^ n ≤ TeschlODE.Shared.symDist N x y) := by sorry

end TeschlODE.IntervalMaps
