-- Prove2me | Theorems.Thm_SpatialSorting_small_changes_magnetization
-- name    : SpatialSorting.small_changes_magnetization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:44:42.205466+00:00
-- url     : https://prove2.me/theorems/15c6f345-f0fb-4cb2-95f6-89a85a46c54c
-- title:
--   Lemma 6.2 — small changes in magnetization
-- statement:
--   Let $A$ be a cost matrix, $\beta\ge0$, $\mathbf h\in\mathbb R^q$, $j$ a colour and $V$ a finite region with pinned collar $F(V)$ and free sites $U=V\setminus F(V)$. For a count vector $\mathbf m$ write $u_i=m_i-|F(V)|\mathbb 1_{i=j}$ (the free-site counts), call $\mathbf m$ *feasible* if $\sum_im_i=|V|$ and all $u_i\ge0$, and let $D_\beta=6\beta A_{\max}+2\|\mathbf h\|_\infty$. Write $\mathcal Z_{j,\mathbf m}(V)$ for the ordinary fixed-count partition function.
--
--   1. For distinct colours $a,b$ and feasible count vectors $\mathbf m$ and $\mathbf m'=\mathbf m-\mathbf e_a+\mathbf e_b$ with $u_a\ge1$,
--   $$e^{-D_\beta}\frac{u_a}{u_b+1}\le\frac{\mathcal Z_{j,\mathbf m'}(V)}{\mathcal Z_{j,\mathbf m}(V)}\le e^{D_\beta}\frac{u_a}{u_b+1}.\tag{31}$$
--   2. If $\mathbf m$ and $\mathbf m'$ are feasible and both free-count vectors have every entry at least $\lambda|U|$, where $\lambda>0$, then
--   $$\Bigl|\log\frac{\mathcal Z_{j,\mathbf m'}(V)}{\mathcal Z_{j,\mathbf m}(V)}\Bigr|\le\frac{D_\beta+\log(1/\lambda)}2\,\|\mathbf m'-\mathbf m\|_1.\tag{32}$$
--
--   Moving a bounded number of units between colours costs only a bounded factor, which is how the exact integer inventory is enforced at controlled cost.
--
--   Differences from the source:
--   - generalization: D_β = 6βA_max + 2‖h*_β‖_∞, at the coexistence field h*_β → every field h, with D_β = 6βA_max + 2‖h‖_∞, and every β ≥ 0; reason: the double-counting proof uses only |h_i| ≤ ‖h‖_∞ and six edges per recolored site; at h = h*_β it is the printed statement
--   - encoding: m′ = m − e_a + e_b → m′_a + 1 = m_a, m′_b = m_b + 1 and m′_i = m_i otherwise, as natural numbers; reason: the same vector equation without natural-number subtraction
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.2, p. 35 (PDF p. 36)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_amax
import Definitions.Def_SpatialSorting_pinned
import Definitions.Def_SpatialSorting_ZordFix
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 6.2 — small changes in magnetization.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.2, p. 35 (PDF p. 36).

Formalization Notes:
- generalization: D_β = 6βA_max + 2‖h*_β‖_∞, at the coexistence field h*_β → every field h, with D_β = 6βA_max + 2‖h‖_∞, and every β ≥ 0. The double-counting proof uses only |h_i| ≤ ‖h‖_∞ and six edges per recolored site; at h = h*_β it is the printed statement.
- encoding: m′ = m − e_a + e_b → m′_a + 1 = m_a, m′_b = m_b + 1 and m′_i = m_i otherwise, as natural numbers. The same vector equation without natural-number subtraction. -/
theorem small_changes_magnetization {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ)
    (hA : IsCostMatrix A) (β : ℝ) (hβ : 0 ≤ β) (h : Fin q → ℝ) (j : Fin q)
    (V : Finset (ℤ × ℤ)) :
    let Dβ := 6 * β * amax A + 2 * ‖h‖
    let feas : (Fin q → ℕ) → Prop := fun m => ∑ i, m i = V.card ∧ (pinned V).card ≤ m j
    let u : (Fin q → ℕ) → Fin q → ℝ := fun m i =>
      (m i : ℝ) - ((pinned V).card : ℝ) * (if i = j then 1 else 0)
    (∀ (a b : Fin q) (m m' : Fin q → ℕ), a ≠ b → feas m → feas m' →
      (m' a + 1 = m a ∧ m' b = m b + 1 ∧ ∀ i, i ≠ a → i ≠ b → m' i = m i) → 1 ≤ u m a →
      Real.exp (-Dβ) * (u m a / (u m b + 1)) ≤ ZordFix A β h j V m' / ZordFix A β h j V m ∧
      ZordFix A β h j V m' / ZordFix A β h j V m ≤ Real.exp Dβ * (u m a / (u m b + 1))) ∧
    ∀ (m m' : Fin q → ℕ) (lam : ℝ), 0 < lam → feas m → feas m' →
      (∀ i, lam * ((V \ pinned V).card : ℝ) ≤ u m i) →
      (∀ i, lam * ((V \ pinned V).card : ℝ) ≤ u m' i) →
      |Real.log (ZordFix A β h j V m' / ZordFix A β h j V m)| ≤
        (Dβ + Real.log (1 / lam)) / 2 * ∑ i, |(m' i : ℝ) - (m i : ℝ)| := by sorry

end SpatialSorting
