-- Prove2me | Theorems.Thm_PubFrequency_lemma_EC_6
-- name    : PubFrequency.lemma_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:03.411423+00:00
-- url     : https://prove2.me/theorems/2114b063-5b25-4238-8e7c-091e8e2c549a
-- title:
--   Lemma EC.6, p. ec2 — the system (11) has a unique solution with $u_1\in[0,1/\alpha]$, $u_2\ge0$, and $\sqrt{2k/\alpha}<u_1^*<1.77\sqrt{k/\alpha}$, $u_2^*>2/\alpha$
-- statement:
--   Let $\alpha>0$ and $k>0$ with $\alpha k<1/2$. Consider the system (11)
--   $$u_1=\sqrt{\frac{2ku_2}{\alpha u_2-1}},\qquad u_2=\frac{\bigl(\sqrt{6\alpha k+1}+2\bigr)(2-\alpha u_1)}{2\alpha(1-2\alpha k)}$$
--   on $u_1\in[0,1/\alpha]$, $u_2\in[0,+\infty)$. It has exactly one solution $(u_1^*,u_2^*)$, and
--   $$\sqrt{\frac{2k}{\alpha}}<u_1^*<1.77\sqrt{\frac{k}{\alpha}},\qquad u_2^*>\frac{2}{\alpha}.$$
--
--   This identifies the equilibrium cycles of Theorem 2 and places them in the regime $\alpha u_1^*<1<2<\alpha u_2^*$.
--
--   **Formalization Note** The constant $1.77$ is the rational $177/100$.
--
--   Differences from the source:
--   - encoding: (11) with √ and a division → Real.sqrt (0 on negatives) and real division (x/0 = 0); reason: if αu₂ ≤ 1 the first equation gives u₁ = 0, and then the second gives u₂ ≥ 3/(2α) > 1/α, a contradiction, so no spurious solution appears
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), Lemma EC.6, p.ec2 (PDF 31)

import Mathlib

namespace PubFrequency

/-- **Lemma EC.6**, Chen–Roels, *Fast or Slow? Competing on Publication Frequency*, SSRN 3986163
(INSEAD WP 2021/74/TOM), p. ec2 (PDF 31). Let `α > 0`, `k > 0` with `α k < 1/2`. The system (11)
`u₁ = √(2k u₂/(α u₂ − 1))`, `u₂ = (√(6αk + 1) + 2)(2 − α u₁)/(2α(1 − 2αk))`
has exactly one solution `(u₁*, u₂*)` with `u₁ ∈ [0, 1/α]` and `u₂ ∈ [0, +∞)`; moreover
`√(2k/α) < u₁* < 1.77 √(k/α)` and `u₂* > 2/α`.

**Formalization Note.** Lean's `Real.sqrt` is `0` on negative arguments and `x / 0 = 0`. These
conventions add no solution: if `α u₂ ≤ 1` the first equation gives `u₁ = 0`, and then the second
gives `u₂ ≥ 3/(2α) > 1/α`, a contradiction. `1.77` is written `177/100`. -/
theorem lemma_EC_6 (α k : ℝ) (hα : 0 < α) (hk : 0 < k) (hαk : α * k < 1 / 2) :
    ∃ a b : ℝ,
      (0 ≤ a ∧ a ≤ 1 / α ∧ 0 ≤ b ∧
        a = Real.sqrt (2 * k * b / (α * b - 1)) ∧
        b = (Real.sqrt (6 * α * k + 1) + 2) * (2 - α * a) / (2 * α * (1 - 2 * α * k))) ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ 1 / α → 0 ≤ y →
        x = Real.sqrt (2 * k * y / (α * y - 1)) →
        y = (Real.sqrt (6 * α * k + 1) + 2) * (2 - α * x) / (2 * α * (1 - 2 * α * k)) →
        x = a ∧ y = b) ∧
      Real.sqrt (2 * k / α) < a ∧ a < (177 / 100 : ℝ) * Real.sqrt (k / α) ∧ 2 / α < b := by sorry

end PubFrequency
