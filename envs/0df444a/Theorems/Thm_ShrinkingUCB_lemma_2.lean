-- Prove2me | Theorems.Thm_ShrinkingUCB_lemma_2
-- name    : ShrinkingUCB.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:22.37358+00:00
-- url     : https://prove2.me/theorems/a8b812f5-17c2-4852-8221-da3230a39d34
-- title:
--   Lemma 2 (corrected: $2\le KT$) — the sum of widths is at most $5\sqrt{dKT\log(KT)}$
-- statement:
--   Let $K,T$ satisfy $KT\ge2$, and let $x_{(t,k)}\in\mathbb R^d$, $t\in[T]$, $k\in[K]$, be any vectors with $\|x_{(t,k)}\|\le1$. With the matrices $A_{t,k}$ of the array,
--
--   $$
--   \sum_{t=1}^T\sum_{k=1}^K\|x_{(t,k)}\|_{A_{t,k-1}^{-1}}\le5\sqrt{dKT\log(KT)},
--   $$
--
--   where $\|v\|_{A^{-1}}=\sqrt{v^\top A^{-1}v}$. This bounds the total width collected over $KT$ selections made one at a time. It gives the variable cost of the regret bound.
--
--   Differences from the source:
--   - correction: Lemma 2 for all K, T → 2 ≤ KT; reason: false at KT = 1: for d = N = K = T = 1, x₁ = 1, θ* = 1/2 every assumption holds, the left side is 1 and the right side is 5√0 = 0
--   - generalization: if we run SemiUCB with ω = 1 → any vectors x_{(t,k)} with ‖x_{(t,k)}‖ ≤ 1; reason: the page applies the lemma to ConsUCB too (p.19), and the bound uses only the norms; both runs are such arrays
--   - reading: log(KT) → Real.log, the natural logarithm; reason: §4 writes ln throughout, and the log of Lemma 2 comes from Chu et al. (2011), whose logarithm is natural; the base changes the bound, so this is a reading, not an encoding
--   - encoding: A⁻¹ → Matrix.inv, total with value 0 on singular matrices; reason: every A_t and A_{t,k} dominates the identity, so the inverse is a true inverse
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, Lemma 2, p.11

import Definitions.Def_ShrinkingUCB_designMatrix

open Matrix

namespace ShrinkingUCB

/-- Lemma 2, p.11 of arXiv:1903.07844v2, corrected: for `2 ≤ KT` and any vectors `x_{(t,k)}` in
the unit ball,
`∑_{t=1}^T ∑_{k=1}^K ‖x_{(t,k)}‖_{A_{t,k-1}⁻¹} ≤ 5√(d K T log(KT))`.

**Formalization Note.** At `d = K = T = 1`, `x = 1` the printed form reads `1 ≤ 0`, which is why
`2 ≤ KT` is needed. -/
theorem lemma_2 {d : ℕ} (K T : ℕ) (hKT : 2 ≤ K * T) (v : ℕ → ℕ → Fin d → ℝ)
    (hv : ∀ t ∈ Finset.Icc 1 T, ∀ k ∈ Finset.Icc 1 K, √(v t k ⬝ᵥ v t k) ≤ 1) :
    ∑ t ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 K,
        √(v t k ⬝ᵥ (designMatrix v K t (k - 1))⁻¹ *ᵥ v t k) ≤
      5 * √((d : ℝ) * K * T * Real.log ((K : ℝ) * T)) := by sorry

end ShrinkingUCB
