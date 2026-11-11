-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_C_1
-- name    : PriceIgnorance.Pairwise.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:25.366186+00:00
-- url     : https://prove2.me/theorems/11c8dc8d-5392-4a44-a8d7-c7742b551e2f
-- title:
--   Lemma C.1 — a finite-image rounding $f(x)\le x$ keeps a $(1-\varepsilon)$ fraction of the prophet's value under every $kI$ law
-- statement:
--   Fix $k$ and $\varepsilon>0$. Let $D_1,\dots,D_n$ be laws of nonnegative values with finite expectations. Then there is a measurable map $f:\mathbb R\to\mathbb R$ such that
--
--   1. $f$ has finite image, $|\mathrm{Im}(f)|<\infty$;
--   2. $f(x)\le x$ for all $x\ge0$;
--   3. for every $D\in kI(D_1,\dots,D_n)$,
--   $$\mathbb E_{V\sim D}\Big[\max_i f(V_i)\Big]\ \ge\ (1-\varepsilon)\,\mathbb E_{V\sim D}\Big[\max_i V_i\Big].$$
--
--   The same $f$ works for every joint law in $kI$. This is the discretization behind Lemma 3.3 and behind the finite-support witnesses that Theorem 1.2 feeds to Theorems 3.16 and 3.19.
--
--   Differences from the source:
--   - reading: f(x) ≤ x (for all x ∈ R) → f(x) ≤ x for all x ≥ 0; reason: values are nonnegative (p. 1) and the proof states 'f(x) ≤ x for all x ≥ 0' (p. 27); a finite-image f cannot satisfy f(x) ≤ x on all of R (recorded as a typo in INSIGHTS.yaml)
--   - reading: a deterministic mapping f : R → R → a measurable f : ℝ → ℝ; reason: f(V_i) must be a random variable for E[max_i f(V_i)] to be defined; the paper's f is measurable
--   - encoding: marginals D_1..D_n with finite expectations → value laws (probability measures on [0, ∞)) that are integrable; reason: standing assumption that values are nonnegative (p. 1)
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 26, Lemma C.1 (proof pp. 26–27)

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_Instance

open MeasureTheory

namespace PriceIgnorance.Pairwise

/-- Lemma C.1 (p. 26): for `ε > 0` and marginals `D_1, …, D_n` of nonnegative values with finite
means there is a measurable `f : ℝ → ℝ` with finite image and `f(x) ≤ x` for `x ≥ 0` such that
`E_D[max_i f(V_i)] ≥ (1 - ε) E_D[max_i V_i]` for every `D ∈ kI(D_1, …, D_n)`. -/
theorem lemma_C_1 (k : ℕ) (ε : ℝ) (hε : 0 < ε) {n : ℕ} (Dm : Fin n → Measure ℝ)
    (hlaw : ∀ i, IsValueLaw (Dm i)) (hint : ∀ i, Integrable id (Dm i)) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (Set.range f).Finite ∧ (∀ x, 0 ≤ x → f x ≤ x) ∧
      ∀ D ∈ kI Dm k, (1 - ε) * ∫ v, (⨆ i, v i) ∂D ≤ ∫ v, (⨆ i, f (v i)) ∂D := by sorry

end PriceIgnorance.Pairwise
