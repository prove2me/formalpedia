-- Prove2me | Theorems.Thm_PelagicFF_fact_3_5
-- name    : PelagicFF.fact_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:54:37.299096+00:00
-- url     : https://prove2.me/theorems/c8fa6fea-c95e-47bb-972b-7baebd13f4a7
-- title:
--   Fact 3.5 — Gaussian estimates with $a=\sqrt{2/3}$, $p^*=0.6$
-- statement:
--   Let $Z\sim N(0,1)$, $a=\sqrt{2/3}$ and $p^*=0.6<2/3$. Then
--   $$\mathbb E\big[Z^2\mathbf 1\{|Z|\le a\}\big]<\frac18,\qquad \mathbb E\big[Z^2\mathbf 1\{|Z|>3a\}\big]<\frac18,\qquad \sup_{b\in\mathbb R}\Pr\big[a\le|b+Z|\le3a\big]<p^* .$$
--
--   The first two estimates make the window $[a,3a]$ contain every Pelagic coefficient of a uniformly random function (Lemma 3.7); the third bounds the window probability (Lemma 3.6).
--
--   **Formalization Note** The expectations are lower Lebesgue integrals of $Z^2$ over the events against `gaussianReal 0 1`; the supremum is taken in $[0,\infty]$, so the strict inequality bounds the supremum, not each $b$ separately.
--
--   Differences from the source:
--   - encoding: E[Z² 1{…}] → ∫⁻ over the event of ofReal(z²) against gaussianReal 0 1; reason: the integrand is nonnegative; same value, no integrability junk
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Fact 3.5, p.23

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PelagicFF

/-- **Fact 3.5 (Gaussian estimates).** Let `Z ∼ N(0,1)`, `a = √(2/3)` and `p∗ = 0.6`. Then
`E[Z² 1{|Z| ≤ a}] < 1/8`, `E[Z² 1{|Z| > 3a}] < 1/8` and `sup_{b ∈ ℝ} Pr[a ≤ |b + Z| ≤ 3a] < p∗`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Fact 3.5, p.23.

**Formalization Note.** The two expectations are lower Lebesgue integrals of `Z²` over the events
against `gaussianReal 0 1` (no integrability junk); the supremum is an `iSup` in `ℝ≥0∞`, so the
strict bound is on the supremum itself, not pointwise in `b`. -/
theorem fact_3_5 :
    (∫⁻ z in {z : ℝ | |z| ≤ Real.sqrt (2 / 3)}, ENNReal.ofReal (z ^ 2) ∂(gaussianReal 0 1)) <
      ENNReal.ofReal (1 / 8) ∧
    (∫⁻ z in {z : ℝ | 3 * Real.sqrt (2 / 3) < |z|}, ENNReal.ofReal (z ^ 2) ∂(gaussianReal 0 1)) <
      ENNReal.ofReal (1 / 8) ∧
    (⨆ b : ℝ, gaussianReal 0 1
        {z | Real.sqrt (2 / 3) ≤ |b + z| ∧ |b + z| ≤ 3 * Real.sqrt (2 / 3)}) <
      ENNReal.ofReal (3 / 5) := by sorry

end PelagicFF
