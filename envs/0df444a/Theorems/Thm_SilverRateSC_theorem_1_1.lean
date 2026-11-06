-- Prove2me | Theorems.Thm_SilverRateSC_theorem_1_1
-- name    : SilverRateSC.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:22.389232+00:00
-- url     : https://prove2.me/theorems/900d6680-99ed-4b0c-8497-3885113baea4
-- title:
--   Theorem 1.1 — $\min\{D_{n,\kappa}(H),E_{n,\kappa}(H)\}\ge\exp[-C_1n\kappa^{-1/p_{\rm sil}}\log\kappa\,e^{C_2\sqrt{\log\kappa}}]$
-- statement:
--   There are absolute constants $C_1,C_2,\kappa_0>0$ such that, for every $\kappa\ge\kappa_0$, every integer $n\ge1$, and every predetermined nonnegative schedule $H\in[0,\infty)^n$,
--   $$\min\{D_{n,\kappa}(H),E_{n,\kappa}(H)\}\ge\exp\Bigl[-C_1\,n\,\kappa^{-1/p_{\rm sil}}\log\kappa\;e^{C_2\sqrt{\log\kappa}}\Bigr],$$
--   where $D_{n,\kappa}$, $E_{n,\kappa}$ are the worst-case ratios (1) over $\tfrac1\kappa$-strongly convex $1$-smooth functions and $p_{\rm sil}=\log_2(1+\sqrt2)$.
--
--   Consequently, reducing either error by a factor $\varepsilon$ with predetermined nonnegative stepsizes needs $\kappa^{1/p_{\rm sil}-o(1)}\log(1/\varepsilon)$ steps: the silver stepsize schedule of Altschuler and Parrilo is optimal up to a subpolynomial factor in $\kappa$.
--
--   Differences from the source:
--   - encoding: absolute constants C_1, C_2, κ_0 > 0 → ∃ C₁ C₂ κ₀ > 0 quantified before κ and H; reason: same
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n with n ≥ 1 → H : List ℝ with nonnegative entries and n = H.length ≥ 1; reason: same schedules
--   - encoding: D_{n,κ}(H), E_{n,κ}(H) as suprema of real ratios → worstDist, worstGap valued in ℝ≥0∞; the bound is ENNReal.ofReal of the real right-hand side; reason: the suprema are finite (proved in the verification file), so the comparison is the paper's
--   - encoding: F_{1/κ,1}(ℝ^d) → HighResODE.NAGSC.IsS1 F κ⁻¹ 1, which also asks 0 < κ⁻¹ ≤ 1; reason: identical for κ ≥ 1; for κ < 1 the paper's class is empty in every dimension d ≥ 1 as well
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the paper pairs log with exp; another base changes only the constants
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Theorem 1.1, (2), p.5; ratios (1), p.5

import Mathlib
import Definitions.Def_SilverRateLB_pSil
import Definitions.Def_SilverRateSC_worstDist
import Definitions.Def_SilverRateSC_worstGap

open scoped ENNReal

namespace SilverRateSC

/-- **Theorem 1.1 (Convergence lower bound).** There are absolute constants `C_1, C_2, κ_0 > 0`
such that, for every `κ ≥ κ_0`, every integer `n ≥ 1`, and every predetermined nonnegative
schedule `H ∈ [0, ∞)^n`,
`min{D_{n,κ}(H), E_{n,κ}(H)} ≥ exp[−C_1 n κ^{−1/p_sil} log κ e^{C_2 √log κ}]` (2).

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Theorem 1.1, (2), p. 5 (ratios (1), p. 5).

**Formalization Note** `C_1, C_2, κ_0` are chosen before `κ` and `H`. The schedule is a `List ℝ`
with nonnegative entries, `n` is its length. `D_{n,κ}`, `E_{n,κ}` are `worstDist`, `worstGap`
(suprema in `ℝ≥0∞`, finite by the verification file), so the bound is `ENNReal.ofReal` of the
real right-hand side. `log` is natural, `κ^{−1/p_sil}` is a real power, `p_sil` is
`SilverRateLB.pSil`. -/
theorem theorem_1_1 :
    ∃ C₁ C₂ κ₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < κ₀ ∧
      ∀ κ : ℝ, κ₀ ≤ κ → ∀ H : List ℝ, 1 ≤ H.length → (∀ x ∈ H, 0 ≤ x) →
        ENNReal.ofReal (Real.exp (-C₁ * H.length * κ ^ (-1 / SilverRateLB.pSil) *
            Real.log κ * Real.exp (C₂ * Real.sqrt (Real.log κ)))) ≤
          min (worstDist κ H) (worstGap κ H) := by sorry

end SilverRateSC
