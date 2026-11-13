-- Prove2me | Theorems.Thm_StaticCalendar_lemma_EC_7
-- name    : StaticCalendar.lemma_EC_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:25:10.203946+00:00
-- url     : https://prove2.me/theorems/5dd47bf8-4975-4646-b2fa-906f15bb4d6f
-- title:
--   Lemma EC.7 — the increasing-weights companion of Lemma EC.4
-- statement:
--   Let $a_i,b_i>0$ for $i=0,\dots,n$ with $a_0/b_0\ge a_1/b_1\ge\dots\ge a_n/b_n$, and let $0\le\beta_0\le\beta_1\le\dots\le\beta_n$. Then
--
--   $$
--   \frac{\sum_{i=0}^na_i}{\sum_{i=0}^nb_i}\ \ge\ \frac{\sum_{i=0}^n\beta_ia_i}{\sum_{i=0}^n\beta_ib_i}.
--   $$
--
--   Weights that increase as the ratios decrease can only lower the mediant. It serves the proof of Lemma EC.5.
--
--   Differences from the source:
--   - reading: "$a_i,b_i>0$, $\forall i\in[n]$" with indices running over $0,\dots,n$ → positivity for $i=0,\dots,n$; reason: the printed ratio $a_0/b_0$ needs $b_0>0$
--   - encoding: no condition that some $\beta_i$ is positive → hypothesis $\exists i,\ \beta_i>0$; reason: it excludes only the case in which the right side is $0/0$
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Lemma EC.7, p.ec6

import Mathlib

namespace StaticCalendar

/-- Lemma EC.7, arXiv:1811.01077v5, p.ec6: for `aᵢ, bᵢ > 0` with `a₀/b₀ ≥ ⋯ ≥ aₙ/bₙ` and
`0 ≤ β₀ ≤ ⋯ ≤ βₙ`, `Σ aᵢ / Σ bᵢ ≥ Σ βᵢaᵢ / Σ βᵢbᵢ`.

**Formalization Note.** The indices run over `0,…,n`, encoded by `Fin (n + 1)`. The hypothesis
`∃ i, 0 < β i` excludes only the case in which the printed right side is `0/0`. -/
theorem lemma_EC_7 {n : ℕ} (a b β : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hratio : Antitone fun i => a i / b i) (hβ : Monotone β) (hβ0 : ∀ i, 0 ≤ β i)
    (hβpos : ∃ i, 0 < β i) :
    (∑ i, β i * a i) / (∑ i, β i * b i) ≤ (∑ i, a i) / (∑ i, b i) := by sorry

end StaticCalendar
