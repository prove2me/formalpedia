-- Prove2me | Theorems.Thm_PRUPermLayer_proposition_4_3
-- name    : PRUPermLayer.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:34.409204+00:00
-- url     : https://prove2.me/theorems/39b088d7-2206-47e9-8e7c-044771a9635f
-- title:
--   Proposition 4.3 — DNP concentration for product layers, (13) and (14)
-- statement:
--   Let $\mu$ be a distribution on $U(2)$, $N = 2^n$, and $t \ge 1$ with $t \le N/2$. Let
--   $$
--   a = \binom t2 \delta_{\mathrm{eq}}(\mu)^n, \qquad b = t\,\lambda_+(\mu)^n, \qquad \gamma = \gamma_t = \frac{t(t-1)}{N - t + 1}.
--   $$
--   Then
--   $$
--   \eta_t(\mu^{\otimes n}) \le \min\{1,\ 4a + 4b + \gamma\}, \tag{13}
--   $$
--   and if $\gamma < 1$,
--   $$
--   \eta_t(\mu^{\otimes n}) \le \frac{a + b + 2\sqrt{\gamma a b}}{1 - \gamma}. \tag{14}
--   $$
--
--   Combined with Lemma 3.1, (13) gives Theorem 1.1(i) and (14) the upper half of Theorem 1.1(ii). Both displays are stated.
--
--   Differences from the source:
--   - encoding: $t \le N/2$ → $2t \le 2^n$ in $\mathbb N$; reason: equivalent for integers
--   - encoding: a distribution $\mu$ on $U(2)$ → a Borel probability measure on $U(2)$; reason: same objects
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Proposition 4.3, Eqs. (13)–(14), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PRUPermLayer_eta
import Definitions.Def_PRUPermLayer_layerLaw
import Definitions.Def_PRUPermLayer_deltaEq
import Definitions.Def_PRUPermLayer_lambdaPlus
import Definitions.Def_PRUPermLayer_gammaT
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Proposition 4.3** (DNP concentration for product layers; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Proposition 4.3, displays
(13) and (14), p.18 (PDF p.20)). Let `µ` be a distribution on `U(2)` and `t ≥ 1` with `t ≤ N/2`,
`N = 2ⁿ`. Let `a = C(t, 2) δ_eq(µ)ⁿ`, `b = t λ₊(µ)ⁿ` and `γ = γ_t = t(t − 1)/(N − t + 1)`. Then
`η_t(µ^{⊗n}) ≤ min{1, 4a + 4b + γ}` (13), and if `γ < 1`,
`η_t(µ^{⊗n}) ≤ (a + b + 2√(γab))/(1 − γ)` (14).

**Formalization Note** `t ≤ N/2` is `2 * t ≤ 2 ^ n` in `ℕ`; `a`, `b`, `γ` are written out. -/
theorem proposition_4_3 (μ : Measure (Matrix.unitaryGroup Bool ℂ)) [IsProbabilityMeasure μ]
    (n t : ℕ) (ht : 1 ≤ t) (htN : 2 * t ≤ 2 ^ n) :
    eta n t (layerLaw μ n) ≤
        min 1 (4 * ((t.choose 2 : ℝ) * deltaEq μ ^ n) + 4 * ((t : ℝ) * lambdaPlus μ ^ n) +
          gammaT (2 ^ n) t) ∧
      (gammaT (2 ^ n) t < 1 →
        eta n t (layerLaw μ n) ≤
          ((t.choose 2 : ℝ) * deltaEq μ ^ n + (t : ℝ) * lambdaPlus μ ^ n +
              2 * Real.sqrt (gammaT (2 ^ n) t * ((t.choose 2 : ℝ) * deltaEq μ ^ n) *
                ((t : ℝ) * lambdaPlus μ ^ n))) / (1 - gammaT (2 ^ n) t)) := by sorry

end PRUPermLayer
