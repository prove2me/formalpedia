-- Prove2me | Theorems.Thm_StabTestMem_tv_le_of_avg_likelihood
-- name    : StabTestMem.tv_le_of_avg_likelihood
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:09:25.26756+00:00
-- url     : https://prove2.me/theorems/99f4715f-26c0-4e96-9482-d50383160f9b
-- title:
--   Lemma 5.3 — an average likelihood-ratio bound controls total variation
-- statement:
--   Let $\mathcal P_1,\mathcal P_2$ be two sets of probability distributions on a discrete set $\Omega$, and let $\mu_1\in\operatorname{conv}\mathcal P_1$, $\mu_2\in\operatorname{conv}\mathcal P_2$. Write $L(x)=\mu_2(x)/\mu_1(x)$. If
--
--   $$\mathbb E_{x\sim\mu_1}\big[|L(x)-1|\big]\le\alpha, \tag{74}$$
--
--   then
--
--   1. $d_{\mathrm{TV}}(\mu_1,\mu_2)=\tfrac12\sum_x|\mu_1(x)-\mu_2(x)|\le2\sqrt\alpha$;
--   2. if $\alpha\le1/36$, no algorithm that sees one sample can distinguish $\mathcal P_1$ from $\mathcal P_2$ with probability at least $2/3$: there is no acceptance rule $D:\Omega\to[0,1]$ that accepts every $P\in\mathcal P_1$ with probability $\ge2/3$ and rejects every $P\in\mathcal P_2$ with probability $\ge2/3$.
--
--   This is the form of Le Cam's method used for both lower bounds.
--
--   Differences from the source:
--   - generalization: distributions in the paper's uses (on finite transcript sets) → probability vectors (nonnegative, summing to 1) on an arbitrary type Ω, sums as tsum; reason: the finite case is a special case; every series is dominated by µ1 + µ2
--   - encoding: an algorithm distinguishing from a single sample → an acceptance probability D(x) ∈ [0, 1]; reason: randomized tests included; Lemma 5.1's single-sample setting
--   - encoding: E_{x∼µ1}|L(x) − 1| with L = µ2/µ1 → Σ_x µ1(x)|µ2(x)/µ1(x) − 1| with a/0 = 0; reason: points with µ1(x) = 0 carry no weight under µ1
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 5.3, p. 37 (L(x) = µ2(x)/µ1(x), p. 36)

import Mathlib

namespace StabTestMem

/-- **Lemma 5.3: an average likelihood-ratio bound controls total variation.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 5.3,
p. 37: "Let P1 and P2 be two sets of distributions. Take distribution µ1 and µ2 in the convex hull of
P1 and P2 respectively. If E_{x∼µ1}[|L(x) − 1|] ≤ α, (74) then d_TV(µ1, µ2) ≤ 2√α. If α ≤ 1/36,
then no algorithm can distinguish between distributions in P1 and P2 with probability at least
2/3." Here `L(x) = µ2(x)/µ1(x)` (p. 36).

Distributions are probability vectors on a discrete set `Ω` (nonnegative, summing to `1`). Under
(74): (1) `(1/2) Σ_x |µ1(x) − µ2(x)| ≤ 2√α`; (2) if `α ≤ 1/36`, no test that sees one sample `x`
and accepts with probability `D(x) ∈ [0, 1]` accepts every `P ∈ P1` with probability `≥ 2/3` and
rejects every `P ∈ P2` with probability `≥ 2/3`.

**Formalization Note.** `Ω` is any type and sums are `tsum` (every series here is dominated by
`µ1 + µ2`, hence summable). In `E_{x∼µ1}|L(x) − 1|` the ratio is literal, with Lean's `a / 0 = 0`
on `µ1(x) = 0`. An algorithm on one sample is its acceptance probability `D(x) ∈ [0, 1]`
(randomized tests included). -/
theorem tv_le_of_avg_likelihood {Ω : Type*} (P₁ P₂ : Set (Ω → ℝ))
    (hP₁ : ∀ P ∈ P₁, (∀ x, 0 ≤ P x) ∧ HasSum P 1) (hP₂ : ∀ P ∈ P₂, (∀ x, 0 ≤ P x) ∧ HasSum P 1)
    (μ₁ μ₂ : Ω → ℝ) (hμ₁ : μ₁ ∈ convexHull ℝ P₁) (hμ₂ : μ₂ ∈ convexHull ℝ P₂) (α : ℝ)
    (hα : ∑' x, μ₁ x * |μ₂ x / μ₁ x - 1| ≤ α) :
    (1 / 2 : ℝ) * ∑' x, |μ₁ x - μ₂ x| ≤ 2 * Real.sqrt α ∧
      (α ≤ 1 / 36 → ¬ ∃ D : Ω → ℝ, (∀ x, 0 ≤ D x ∧ D x ≤ 1) ∧
        (∀ P ∈ P₁, (2 / 3 : ℝ) ≤ ∑' x, D x * P x) ∧
        (∀ P ∈ P₂, (2 / 3 : ℝ) ≤ ∑' x, (1 - D x) * P x)) := by sorry

end StabTestMem
