-- Prove2me | Theorems.Thm_TalagrandConc_TwoPoint_lemma_2_3_5
-- name    : TalagrandConc.TwoPoint.lemma_2_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:02.153986+00:00
-- url     : https://prove2.me/theorems/f591a56b-66f8-41b6-85ea-730177e46271
-- title:
--   Lemma 2.3.5 — the two-point inequality (2.3.8) behind Theorem 2.3.4
-- statement:
--   Let $p,p_1\in[0,1]$ with $p_1>p$ (in Section 2.3, $p=\mu(\{1\})$ and $p_1=\mu_1(\{1\})$ for two probabilities $\mu,\mu_1$ on $\{0,1\}$), let $\alpha>0$, $t\ge 0$, and let
--   $$a(\alpha,t)=\max\Big(1,\ (1-p+pe^{t})\,(p_1e^{-t/\alpha}+1-p_1)^{\alpha}\Big).$$
--
--   Then for all $0\le a\le b\le 1$,
--   $$\frac{1-p}{b^{\alpha}}+p\min\Big(\frac{1}{a^{\alpha}},\frac{e^{t}}{b^{\alpha}}\Big)\le\frac{a(\alpha,t)}{(ap_1+b(1-p_1))^{\alpha}}.$$
--
--   This is the one-coordinate inequality to which the induction on $N$ in the proof of Theorem 2.3.4 reduces; there $a$ and $b$ are the $P_1$-measures of a section of the set $A$ and of its projection.
--
--   **Formalization Note** $a$ and $b$ range over $[0,\infty]$ (`ℝ≥0∞`), so the endpoint $a=0$, which the paper uses for $N=1$, is included with $1/0^{\alpha}=+\infty$ (and $x/0=+\infty$ for $x>0$). The range $\alpha>0$ is read from Section 2.2, where the exponent $\alpha$ of $P(A)$ was introduced; Theorem 2.3.4 does not restate it.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 90, Lemma 2.3.5, Eq. (2.3.8)

import Mathlib
import Definitions.Def_TalagrandConc_TwoPoint_Basic

open MeasureTheory
open scoped ENNReal NNReal

namespace TalagrandConc.TwoPoint

/-- Talagrand (1995), Lemma 2.3.5, Eq. (2.3.8), p. 90. Standing assumptions of §2.3:
`μ({1}) = p`, `μ₁({1}) = p₁ > p`; `t ≥ 0` and `α > 0` as in Theorem 2.3.4.
The numbers `a ≤ b ≤ 1` are taken in `ℝ≥0∞` so that `a = 0` (used in the proof of
Theorem 2.3.4 for `N = 1`) is allowed, with `1 / 0^α = ∞`. -/
theorem lemma_2_3_5 (p p₁ : unitInterval) (hpp₁ : p < p₁)
    (α : ℝ) (hα : 0 < α) (t : ℝ) (ht : 0 ≤ t) (a b : ℝ≥0∞) (hab : a ≤ b) (hb : b ≤ 1) :
    ENNReal.ofReal (1 - (p : ℝ)) / b ^ α
        + ENNReal.ofReal (p : ℝ) * min (1 / a ^ α) (ENNReal.ofReal (Real.exp t) / b ^ α)
      ≤ ENNReal.ofReal (aConst α t (p : ℝ) (p₁ : ℝ))
          / (a * ENNReal.ofReal (p₁ : ℝ) + b * ENNReal.ofReal (1 - (p₁ : ℝ))) ^ α := by sorry

end TalagrandConc.TwoPoint
