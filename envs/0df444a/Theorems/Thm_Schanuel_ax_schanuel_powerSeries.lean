-- Prove2me | Theorems.Thm_Schanuel_ax_schanuel_powerSeries
-- name    : Schanuel.ax_schanuel_powerSeries
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T17:34:04.584374+00:00
-- url     : https://prove2.me/theorems/b525966b-1e51-4d79-b6e5-c17f3825e9e8
-- title:
--   Ax's theorem (Ax–Schanuel) for formal power series
-- statement:
--   **Ax's theorem (Ax–Schanuel), formal power series form.** Let $n \ge 1$ and let $f_1, \dots, f_n$ and $g_1, \dots, g_n$ be formal power series in one variable over $\mathbb{C}$ such that each $g_i$ is invertible in $\mathbb{C}[[X]]$ and satisfies the differential equation
--
--   $$g_i' = f_i' \, g_i ,$$
--
--   where $'$ is formal differentiation; equivalently $g_i = c_i \exp(f_i)$ for a nonzero constant $c_i$ whenever this makes sense. Assume that no nontrivial $\mathbb{Q}$-linear combination $\sum_i q_i f_i$ is a constant series. Then
--
--   $$\operatorname{trdeg}_{\mathbb{C}} \mathbb{C}\bigl[f_1,\dots,f_n,g_1,\dots,g_n\bigr] \;\ge\; n + 1 .$$
--
--   This is the function-field analogue of Schanuel's conjecture, proved by Ax in 1971 for differential fields of characteristic zero; the extra $+1$ reflects the rank of the Jacobian in the one-variable case.
-- source:
--   J. Ax, On Schanuel's conjectures, Annals of Mathematics 93 (1971), 252–268, https://doi.org/10.2307/1970774 (Theorem 1, specialized to one variable)

import Mathlib

namespace Schanuel
theorem ax_schanuel_powerSeries (n : ℕ) (hn : 0 < n) (f g : Fin n → PowerSeries ℂ)
    (hgunit : ∀ i, IsUnit (g i))
    (hexp : ∀ i, PowerSeries.derivative ℂ (g i) = PowerSeries.derivative ℂ (f i) * g i)
    (hfree : ∀ q : Fin n → ℚ, (∃ i, q i ≠ 0) →
      PowerSeries.derivative ℂ (∑ i, (q i : ℂ) • f i) ≠ 0) :
    ((n + 1 : ℕ) : Cardinal) ≤
      Algebra.trdeg ℂ (Algebra.adjoin ℂ (Set.range f ∪ Set.range g)) := by sorry
end Schanuel
