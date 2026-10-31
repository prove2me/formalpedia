-- Prove2me | Theorems.Thm_PeriodicEval_lemma_2
-- name    : PeriodicEval.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:06:47.829994+00:00
-- url     : https://prove2.me/theorems/37a27fcb-e467-4289-8651-1fcc13cc3835
-- title:
--   Lemma 2 — the smallest concave majorant $\bar G_a$ (corrected: $\le 1$ in Case 1; Case 2 excludes $a=-1$, $k=0$)
-- statement:
--   Let $\bar G_a$ be the smallest concave majorant of $G_a$ on $[0,\infty)$, under the standing assumptions, and $\kappa=(k^{1/(1-\alpha)}+1)^{1-\alpha}$.
--
--   1. For $a>0$ there are unique $c_1,c_2$ with $0<c_1<1/(1+(k/a)^{1/(2-\alpha)})\le1<c_2$ solving
--   $$\frac{(c_2-1)^\alpha+ac_2^\alpha+k(1-c_1)^\alpha-ac_1^\alpha}{c_2-c_1}=\alpha[(c_2-1)^{\alpha-1}+ac_2^{\alpha-1}]=\alpha[k(1-c_1)^{\alpha-1}+ac_1^{\alpha-1}]\qquad(20)$$
--   and, with $m_1:=\gamma^{\alpha-1}\frac{(c_2-1)^\alpha+ac_2^\alpha+k(1-c_1)^\alpha-ac_1^\alpha}{c_2-c_1}$ (19),
--   $$\bar G_a(y)=\begin{cases}-k(\gamma-y)^\alpha+ay^\alpha,&0\le y<c_1\gamma,\\-k\gamma^\alpha(1-c_1)^\alpha+ac_1^\alpha\gamma^\alpha+m_1(y-c_1\gamma),&c_1\gamma\le y\le c_2\gamma,\\(y-\gamma)^\alpha+ay^\alpha,&y>c_2\gamma.\end{cases}$$
--   2. For $-1\le a\le0$ with $(a,k)\neq(-1,0)$ there is a unique $c_3>1$ solving
--   $$\frac{(c_3-1)^\alpha+ac_3^\alpha+k}{c_3}=\alpha[(c_3-1)^{\alpha-1}+ac_3^{\alpha-1}]\qquad(22)$$
--   and, with $m_2:=\gamma^{\alpha-1}\frac{(c_3-1)^\alpha+ac_3^\alpha+k}{c_3}$ (21), $\bar G_a(y)=-k\gamma^\alpha+m_2y$ for $0\le y\le c_3\gamma$ and $\bar G_a(y)=(y-\gamma)^\alpha+ay^\alpha$ for $y>c_3\gamma$.
--   3. For $-\kappa<a<-1$ there is a unique $c_3$ with $1<c_3<1/(1-|a|^{-1/(1-\alpha)})$ solving (22), and
--   $$\bar G_a(y)=\begin{cases}-k\gamma^\alpha+m_2y,&0\le y\le c_3\gamma,\\(y-\gamma)^\alpha+ay^\alpha,&c_3\gamma<y<\gamma/(1-|a|^{-1/(1-\alpha)}),\\-\gamma^\alpha|a|(1-|a|^{-1/(1-\alpha)})^{1-\alpha},&y\ge\gamma/(1-|a|^{-1/(1-\alpha)}).\end{cases}$$
--   4. For $a\le-\kappa$, $\bar G_a(y)=-k\gamma^\alpha$ for all $y\ge0$.
--
--   These are the shapes that determine the optimizer of the auxiliary problem (Proposition 3).
--
--   **Formalization Note** At $\gamma=0$ the factor $\gamma^{\alpha-1}$ in $m_1,m_2$ is Lean's $0^{\alpha-1}=0$; it multiplies an interval of length zero, so the formulas are unaffected.
--
--   Differences from the source:
--   - correction: 0 < c1 < 1/(1+(k/a)^{1/(2−α)}) < 1 < c2 → … ≤ 1 < c2; reason: at k = 0 (allowed, k ≥ 0, p.8) the middle term equals 1 and '1 < 1' is false for every a > 0, γ, α
--   - correction: Case 2 for all −1 ≤ a ≤ 0 → Case 2 for −1 ≤ a ≤ 0 with (a, k) ≠ (−1, 0); reason: at k = 0, a = −1, any γ > 0: G_{−1} < 0 on (0, ∞), G_{−1}(0) = 0 and G_{−1} → 0, so Ḡ_{−1} ≡ 0, while (22) has no root c3 > 1 (its left side is negative, its right side positive); Case 4 covers this point
--   - reading: 'c1, c2 … are the solutions to (20)', 'c3 is the solution to (22)' → existence and uniqueness; in Case 3 uniqueness within 1 < c3 < 1/(1 − |a|^{−1/(1−α)}); reason: 'the solutions' asserts uniqueness; in Case 3, (22) has a second root beyond the maximum of G_a, and the tangency point of the proof lies before it (p.35)
--   - encoding: m1, m2 with the factor γ^{α−1} → Lean's 0^{α−1} = 0 at γ = 0; reason: at γ = 0 the factor multiplies an interval of length zero; for γ > 0 it is the paper's power
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Lemma 2, eqs. (19)–(22), pp.33–34

import Mathlib
import Definitions.Def_PeriodicEval_Utility
import Definitions.Def_PeriodicEval_Concavify

open Set

namespace PeriodicEval

/-- Lemma 2 (corrected), SSRN 3971852 (June 20, 2023), pp.33–34: the smallest concave majorant
`Ḡ_a` of `G_a` on `[0, ∞)`, in four regimes of `a`.

1. For `a > 0` there are unique `c₁, c₂` with `0 < c₁ < 1/(1 + (k/a)^{1/(2−α)}) ≤ 1 < c₂`
   solving the system (20), and with `m₁` of (19),
   `Ḡ_a(y) = −k(γ − y)^α + a y^α` on `0 ≤ y < c₁γ`,
   `Ḡ_a(y) = −kγ^α(1 − c₁)^α + a c₁^α γ^α + m₁(y − c₁γ)` on `c₁γ ≤ y ≤ c₂γ`,
   `Ḡ_a(y) = (y − γ)^α + a y^α` on `y > c₂γ`.
2. For `−1 ≤ a ≤ 0`, `(a, k) ≠ (−1, 0)`, there is a unique `c₃ > 1` solving (22), and with
   `m₂` of (21), `Ḡ_a(y) = −kγ^α + m₂ y` on `[0, c₃γ]` and `(y − γ)^α + a y^α` on `y > c₃γ`.
3. For `−κ < a < −1` there is a unique `c₃` with `1 < c₃ < 1/(1 − |a|^{−1/(1−α)})` solving
   (22), and `Ḡ_a(y) = −kγ^α + m₂ y` on `[0, c₃γ]`, `(y − γ)^α + a y^α` on
   `c₃γ < y < γ/(1 − |a|^{−1/(1−α)})`, and `−γ^α|a|(1 − |a|^{−1/(1−α)})^{1−α}` beyond.
4. For `a ≤ −κ`, `Ḡ_a ≡ −kγ^α` on `[0, ∞)`.

**Formalization Note** Corrections: the printed `1/(1 + (k/a)^{1/(2−α)}) < 1` is false at
`k = 0` and is replaced by `≤ 1`; Case 2 excludes `(a, k) = (−1, 0)`, where `Ḡ_{−1} ≡ 0` and
(22) has no root. "The solutions" is read as existence and uniqueness; in Case 3 uniqueness is
within the tangency range `c₃ < 1/(1 − |a|^{−1/(1−α)})` (the point of contact lies before the
maximum of `G_a`; (22) has a second root beyond it). At `γ = 0` the factor `γ^{α−1}` in `m₁`,
`m₂` is Lean's `0 ^ (α − 1) = 0`, multiplied by an interval of length zero. -/
theorem lemma_2 (p : Params) (hp : p.Standing) :
    -- 1. a > 0
    (∀ a : ℝ, 0 < a →
      let eq20 : ℝ → ℝ → Prop := fun c₁ c₂ =>
        ((c₂ - 1) ^ p.α + a * c₂ ^ p.α + p.k * (1 - c₁) ^ p.α - a * c₁ ^ p.α) / (c₂ - c₁) =
            p.α * ((c₂ - 1) ^ (p.α - 1) + a * c₂ ^ (p.α - 1)) ∧
          p.α * ((c₂ - 1) ^ (p.α - 1) + a * c₂ ^ (p.α - 1)) =
            p.α * (p.k * (1 - c₁) ^ (p.α - 1) + a * c₁ ^ (p.α - 1))
      let range : ℝ → ℝ → Prop := fun c₁ c₂ =>
        0 < c₁ ∧ c₁ < 1 / (1 + (p.k / a) ^ (1 / (2 - p.α))) ∧
          1 / (1 + (p.k / a) ^ (1 / (2 - p.α))) ≤ 1 ∧ 1 < c₂
      ∃ c₁ c₂ : ℝ, (range c₁ c₂ ∧ eq20 c₁ c₂) ∧
        (∀ d₁ d₂ : ℝ, range d₁ d₂ → eq20 d₁ d₂ → d₁ = c₁ ∧ d₂ = c₂) ∧
        let m₁ := p.γ ^ (p.α - 1) *
          (((c₂ - 1) ^ p.α + a * c₂ ^ p.α + p.k * (1 - c₁) ^ p.α - a * c₁ ^ p.α) / (c₂ - c₁))
        (∀ y : ℝ, 0 ≤ y → y < c₁ * p.γ →
          concaveMajorant (G p a) y = -(p.k * (p.γ - y) ^ p.α) + a * y ^ p.α) ∧
        (∀ y : ℝ, c₁ * p.γ ≤ y → y ≤ c₂ * p.γ →
          concaveMajorant (G p a) y = -(p.k * p.γ ^ p.α * (1 - c₁) ^ p.α) +
            a * c₁ ^ p.α * p.γ ^ p.α + m₁ * (y - c₁ * p.γ)) ∧
        (∀ y : ℝ, c₂ * p.γ < y →
          concaveMajorant (G p a) y = (y - p.γ) ^ p.α + a * y ^ p.α)) ∧
    -- 2. −1 ≤ a ≤ 0 (corrected: (a, k) ≠ (−1, 0))
    (∀ a : ℝ, -1 ≤ a → a ≤ 0 → ¬(a = -1 ∧ p.k = 0) →
      let eq22 : ℝ → Prop := fun c₃ =>
        ((c₃ - 1) ^ p.α + a * c₃ ^ p.α + p.k) / c₃ =
          p.α * ((c₃ - 1) ^ (p.α - 1) + a * c₃ ^ (p.α - 1))
      ∃ c₃ : ℝ, (1 < c₃ ∧ eq22 c₃) ∧ (∀ d : ℝ, 1 < d → eq22 d → d = c₃) ∧
        let m₂ := p.γ ^ (p.α - 1) * (((c₃ - 1) ^ p.α + a * c₃ ^ p.α + p.k) / c₃)
        (∀ y : ℝ, 0 ≤ y → y ≤ c₃ * p.γ →
          concaveMajorant (G p a) y = -(p.k * p.γ ^ p.α) + m₂ * y) ∧
        (∀ y : ℝ, c₃ * p.γ < y →
          concaveMajorant (G p a) y = (y - p.γ) ^ p.α + a * y ^ p.α)) ∧
    -- 3. −κ < a < −1
    (∀ a : ℝ, -p.κ < a → a < -1 →
      let eq22 : ℝ → Prop := fun c₃ =>
        ((c₃ - 1) ^ p.α + a * c₃ ^ p.α + p.k) / c₃ =
          p.α * ((c₃ - 1) ^ (p.α - 1) + a * c₃ ^ (p.α - 1))
      let cmax := 1 / (1 - |a| ^ (-1 / (1 - p.α)))
      ∃ c₃ : ℝ, (1 < c₃ ∧ c₃ < cmax ∧ eq22 c₃) ∧
        (∀ d : ℝ, 1 < d → d < cmax → eq22 d → d = c₃) ∧
        let m₂ := p.γ ^ (p.α - 1) * (((c₃ - 1) ^ p.α + a * c₃ ^ p.α + p.k) / c₃)
        (∀ y : ℝ, 0 ≤ y → y ≤ c₃ * p.γ →
          concaveMajorant (G p a) y = -(p.k * p.γ ^ p.α) + m₂ * y) ∧
        (∀ y : ℝ, c₃ * p.γ < y → y < p.ymax a →
          concaveMajorant (G p a) y = (y - p.γ) ^ p.α + a * y ^ p.α) ∧
        (∀ y : ℝ, p.ymax a ≤ y →
          concaveMajorant (G p a) y =
            -(p.γ ^ p.α * |a| * (1 - |a| ^ (-1 / (1 - p.α))) ^ (1 - p.α)))) ∧
    -- 4. a ≤ −κ
    (∀ a : ℝ, a ≤ -p.κ → ∀ y : ℝ, 0 ≤ y → concaveMajorant (G p a) y = -(p.k * p.γ ^ p.α)) := by sorry

end PeriodicEval
