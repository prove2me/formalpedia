-- Prove2me | Theorems.Thm_WeightedMajority_Randomized_theorem_6_1
-- name    : WeightedMajority.Randomized.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:25.386003+00:00
-- url     : https://prove2.me/theorems/0daad7b8-5b91-40a6-9610-1e6dcbf8887b
-- title:
--   Theorem 6.1 — under the weak independence condition WMR has $\mathbf E(m)\le\mathbf E(\ln(w_{\mathrm{init}}/w_{\mathrm{fin}}))/(1-\beta)$
-- statement:
--   Let the randomized master algorithm WMR run for $t$ trials on a sequence of instances with binary labels $\rho^{(j)} \in \{0,1\}$, using a pool of $n$ (possibly probabilistic) prediction algorithms whose predictions $x_i^{(j)}$ lie in $[0,1]$. The parameter satisfies $0 \le \beta < 1$, the initial weights are positive, and in every trial each weight is multiplied by a factor satisfying (5.1),
--   $$
--   \beta^{|x_i^{(j)}-\rho^{(j)}|} \le F \le 1-(1-\beta)\,|x_i^{(j)}-\rho^{(j)}|.
--   $$
--   WMR predicts $\lambda^{(j)} \in \{0,1\}$, and $m = \sum_{j=1}^t |\lambda^{(j)}-\rho^{(j)}|$ is its number of mistakes. Let $w_{\mathrm{init}}$ and $w_{\mathrm{fin}}$ be the total weights before the first and after the last trial, and assume $w_{\mathrm{fin}} > 0$ almost surely. If the weak independence condition
--   $$
--   \mathbf E\big(\lambda^{(j)} \,\big|\, (x^{(1)},\rho^{(1)}),\dots,(x^{(j)},\rho^{(j)})\big) = \gamma^{(j)} \quad\text{a.s.}, \qquad j = 1,\dots,t,
--   $$
--   holds, then
--   $$
--   \mathbf E(m) \le \frac{\mathbf E\big(\ln(w_{\mathrm{init}}/w_{\mathrm{fin}})\big)}{1-\beta}.
--   $$
--
--   The bound transfers the loss bound of the deterministic weighted-average algorithm WMC to a master whose predictions are binary, the improvement over the deterministic binary master WMG coming from the randomization. When predictions and labels are deterministic it reads $\mathbf E(m) \le \ln(w_{\mathrm{init}}/w_{\mathrm{fin}})/(1-\beta)$.
--
--   **Formalization Note** Both expectations are lower Lebesgue integrals with values in $[0,\infty]$, so the right-hand side may be $+\infty$ (as in the paper) and no integrability of $\ln(w_{\mathrm{init}}/w_{\mathrm{fin}})$ is assumed; the logarithm is nonnegative because every factor is at most $1$. The paper's bound is infinite when $w_{\mathrm{fin}} = 0$, where Lean's $\ln 0 = 0$ would give a false literal statement; the hypothesis $w_{\mathrm{fin}} > 0$ almost surely excludes exactly that case. Trials are indexed from $0$, the initial weights are deterministic, and the update factor is a measurable function of the member's prediction and the label that may depend on the trial and the member.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 240, Theorem 6.1

import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory

namespace WeightedMajority.Randomized

/-- Theorem 6.1 (p. 240): under the weak independence condition, the expected number of
mistakes of WMR is at most `E(ln(w_init/w_fin))/(1 − β)`. Expectations are lower Lebesgue
integrals, so the right-hand side may be `+∞`; `w_fin > 0` almost surely excludes the paper's
infinite-bound case. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam)
    (hfin : ∀ᵐ ω ∂P, 0 < totalWeight w1 F x ρ t ω) :
    ∫⁻ ω, ENNReal.ofReal (mistakes t lam ρ ω) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal
          (Real.log (totalWeight w1 F x ρ 0 ω / totalWeight w1 F x ρ t ω)) ∂P)
        / ENNReal.ofReal (1 - β) := by sorry

end WeightedMajority.Randomized
