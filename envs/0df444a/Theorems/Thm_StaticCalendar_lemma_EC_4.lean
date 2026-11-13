-- Prove2me | Theorems.Thm_StaticCalendar_lemma_EC_4
-- name    : StaticCalendar.lemma_EC_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:25:15.243843+00:00
-- url     : https://prove2.me/theorems/8fadc6bb-e827-4e4c-aab1-976bbc5125f1
-- title:
--   Lemma EC.4 — ordered-weights mediant inequality
-- statement:
--   Let $a_i,b_i>0$ for $i\in[n]$ with $a_1/b_1\ge a_2/b_2\ge\dots\ge a_n/b_n$, and let $\beta_1\ge\beta_2\ge\dots\ge\beta_n\ge0$. Then
--
--   $$
--   \frac{\sum_{i\in[n]}\beta_ia_i}{\sum_{i\in[n]}\beta_ib_i}\ \ge\ \frac{\sum_{i\in[n]}a_i}{\sum_{i\in[n]}b_i}.
--   $$
--
--   Weights that decrease together with the ratios can only raise the mediant. It is the tool behind (EC.5).
--
--   Differences from the source:
--   - encoding: no condition that some $\beta_i$ is positive → hypothesis $\exists i,\ \beta_i>0$; reason: it excludes only the case in which the left side is $0/0$
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Lemma EC.4, p.ec4

import Mathlib

namespace StaticCalendar

/-- Lemma EC.4, arXiv:1811.01077v5, p.ec4: for `aᵢ, bᵢ > 0` with `a₁/b₁ ≥ ⋯ ≥ aₙ/bₙ` and
`β₁ ≥ ⋯ ≥ βₙ ≥ 0`, `Σ βᵢaᵢ / Σ βᵢbᵢ ≥ Σ aᵢ / Σ bᵢ`.

**Formalization Note.** The hypothesis `∃ i, 0 < β i` excludes only the case in which the printed
left side is `0/0`. -/
theorem lemma_EC_4 {n : ℕ} (a b β : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hratio : Antitone fun i => a i / b i) (hβ : Antitone β) (hβ0 : ∀ i, 0 ≤ β i)
    (hβpos : ∃ i, 0 < β i) :
    (∑ i, a i) / (∑ i, b i) ≤ (∑ i, β i * a i) / (∑ i, β i * b i) := by sorry

end StaticCalendar
