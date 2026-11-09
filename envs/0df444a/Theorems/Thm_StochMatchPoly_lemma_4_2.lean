-- Prove2me | Theorems.Thm_StochMatchPoly_lemma_4_2
-- name    : StochMatchPoly.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:14:15.0522+00:00
-- url     : https://prove2.me/theorems/8b896880-357e-42eb-a4b9-11f15e0cbd29
-- title:
--   Lemma 4.2 — the positive-part bound $\mathbb E(W-c)_+\le\mathrm{Var}(W)/(4(c-\mathbb E W))$
-- statement:
--   1. For $b>0$ and $r\in\mathbb R$,
--   $$(r-b)_+\le\frac{r^2}{4b},\qquad (r)_+:=\max\{r,0\}.$$
--   2. Consequently, if $W$ is a real random variable with finite variance and $c>\mathbb E W$, then
--   $$\mathbb E(W-c)_+\le\frac{\operatorname{Var}(W)}{4(c-\mathbb E W)}.$$
--
--   The second form bounds the expected overload of a vertex in the main proof.
--
--   Differences from the source:
--   - encoding: W has finite variance → MemLp W 2 P on a probability space (Ω, P); reason: finite variance is square integrability, which also gives integrability of W and (W − c)₊
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Lemma 4.2, p.10 (PDF p.11)

import Mathlib

open MeasureTheory ProbabilityTheory

universe u

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Lemma 4.2 (A positive-part bound), p.10 (PDF p.11).

"For b > 0 and r ∈ ℝ, (r − b)₊ ≤ r²/(4b), (r)₊ := max{r, 0}. Consequently, if W has finite
variance and c > E W, then E(W − c)₊ ≤ Var(W)/(4(c − E W))."

**Formalization Note.** The second part is stated for a real random variable `W` on an arbitrary
probability space; "finite variance" is `MemLp W 2 P` (square integrable, which also makes `W`
and `(W − c)₊` integrable), `E W` is the Bochner integral and `Var(W)` is Mathlib's `variance`. -/
theorem lemma_4_2 :
    (∀ b r : ℝ, 0 < b → max (r - b) 0 ≤ r ^ 2 / (4 * b)) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
      (c : ℝ), MemLp W 2 P → ∫ ω, W ω ∂P < c →
      ∫ ω, max (W ω - c) 0 ∂P ≤ variance W P / (4 * (c - ∫ ω, W ω ∂P)) := by sorry

end StochMatchPoly
