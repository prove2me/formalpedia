-- Prove2me | Theorems.Thm_PlugInRisk_lemma_4_6
-- name    : PlugInRisk.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:44.678686+00:00
-- url     : https://prove2.me/theorems/d01674bb-68d6-4a72-b210-0b9898ee4d35
-- title:
--   Lemma 4.6: a dyadic series bound
-- statement:
--   Let $0\le b<a<1$. There is a constant $C>0$ such that for every $x\in[0,\infty)$ the series converges and
--
--   $$
--   \sum_{n\ge1}2^{-an}\bigl((x2^n)\wedge 2^{bn}\bigr)\le C\bigl(x^{(a-b)/(1-b)}\vee x\bigr).
--   $$
--
--   This is the summation step of the multiscale argument in Theorems 4.1 and 5.1.
--
--   Differences from the source:
--
--   - generalization: the assumptions of Theorem 4.1 → dropped; reason: the lemma involves only a, b and x
--   - encoding: Σ_{n≥1} → ∑' over n : ℕ with n + 1 in place of n, summability stated; reason: a real tsum of a non-summable series is 0
--   - encoding: C → C > 0; reason: a bound with some C also holds with any larger positive C
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 4.6, p.20

import Mathlib

namespace PlugInRisk

/-- **Lemma 4.6** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 4.6, p.20): "Let 0 ≤ b < a < 1. Then
it holds that Σ_{n≥1} 2^{−an} · ((x2ⁿ) ∧ 2^{bn}) ≤ C (x^{(a−b)/(1−b)} ∨ x) for every
x ∈ [0, ∞) (where C does not depend on x)."

**Formalization Note** The sum over `n ≥ 1` is written over `n : ℕ` with `n + 1` in place of
`n`. Summability is part of the conclusion (a real `tsum` of a non-summable series is `0`). The
hypotheses of Theorem 4.1 do not occur in the lemma and are omitted. -/
theorem lemma_4_6 (a b : ℝ) (hb : 0 ≤ b) (hba : b < a) (ha : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      Summable (fun n : ℕ => (2 : ℝ) ^ (-(a * ((n : ℝ) + 1))) *
        min (x * (2 : ℝ) ^ ((n : ℝ) + 1)) ((2 : ℝ) ^ (b * ((n : ℝ) + 1)))) ∧
      ∑' n : ℕ, (2 : ℝ) ^ (-(a * ((n : ℝ) + 1))) *
        min (x * (2 : ℝ) ^ ((n : ℝ) + 1)) ((2 : ℝ) ^ (b * ((n : ℝ) + 1)))
        ≤ C * max (x ^ ((a - b) / (1 - b))) x := by sorry

end PlugInRisk
