-- Prove2me | Theorems.Thm_SinglePointPricing_Det_theorem_2
-- name    : SinglePointPricing.Det.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:04.467211+00:00
-- url     : https://prove2.me/theorems/fa63cb38-68f9-4b56-ad4d-6d4214847698
-- title:
--   Theorem 2, pp. 21–22 — deterministic maximin ratio and optimal price from one conversion rate, regular (α = 0) and mhr (α = 1)
-- statement:
--   Fix the deterministic mechanisms $\mathcal P_d = \{\delta_\gamma:\gamma\ge0\}$, a historical price $w>0$ and its conversion rate $q = \overline F(w)\in(0,1)$.
--
--   1. **Regular laws ($\alpha=0$).** The price
--   $$p^*_d(w,q) = w\Big(\tfrac{2\sqrt q}{1+\sqrt q}\mathbf 1\{q\in(0,\tfrac14]\} + \tfrac{q(3-4q)}{1-q}\mathbf 1\{q\in(\tfrac14,\tfrac12]\} + \mathbf 1\{q\in(\tfrac12,1)\}\Big)$$
--   is optimal, and the maximin ratio is
--   $$\mathcal R(\mathcal P_d,\mathcal F_0(w,q)) = \tfrac{2\sqrt q}{1+\sqrt q}\mathbf 1\{q\in(0,\tfrac14]\} + \tfrac{3-4q}{4(1-q)}\mathbf 1\{q\in(\tfrac14,\tfrac12]\} + (1-q)\mathbf 1\{q\in(\tfrac12,1)\}.$$
--   2. **Monotone hazard rate laws ($\alpha=1$).** The price
--   $$p^*_d(w,q) = w\Big(\beta_q\big(\tfrac eq\big)\mathbf 1\{q\in(0,\hat q]\} + \beta_q\big(\tfrac1{\log(q^{-1})}\big)\mathbf 1\{q\in(\hat q,e^{-e^{-1}}]\} + \mathbf 1\{q\in(e^{-e^{-1}},1)\}\Big)$$
--   is optimal, and the maximin ratio is
--   $$\mathcal R(\mathcal P_d,\mathcal F_1(w,q)) = \beta_q\big(\tfrac eq\big)\mathbf 1\{q\in(0,\hat q]\} + \rho(q)\mathbf 1\{q\in(\hat q,e^{-e^{-1}}]\} + eq\log(q^{-1})\mathbf 1\{q\in(e^{-e^{-1}},1)\}.$$
--
--   Here $W$ is the Lambert function (the inverse of $x\mapsto xe^x$ on $[0,\infty)$), $\beta_q(x) = 1-\frac1{\log(q^{-1})}\big(W(x)+\frac1{W(x)}-2\big)$, $\rho(q) = \beta_q\big(\frac1{\log(q^{-1})}\big)e\log(q^{-1})e^{-\log(q^{-1})\beta_q(1/\log(q^{-1}))}$, and $\hat q$ is the unique solution in $[0,1]$ of $W\big(\frac1{\log(q^{-1})}\big)W\big(\frac eq\big) = 1$; numerically $\hat q\in[0.52,0.53]$. "Optimal" means that the worst-case ratio of $\delta_{p^*_d}$ over the whole class $\mathcal F_\alpha(w,q)$ equals the maximin ratio.
--
--   The theorem gives in closed form the value of one observed conversion rate for deterministic pricing and the price to post: for example, about 85% of the oracle revenue is guaranteed for mhr laws when half of the customers bought at $w$.
--
--   Differences from the source:
--   - reading: F̄ = 1 − F for a right-continuous cdf F (p. 9) → F̄(p) = μ([p, ∞)), the closed tail P(v ≥ p); reason: the page defines the data as the fraction of values greater than or equal to w (p. 2), the revenue as ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), and its worst cases (3.1) as ccdfs equal to the atom's size at the top of the support; only the closed tail makes these agree, and the two tails differ only at atoms
--   - reading: α-strong regularity: a positive density on the support [a, b] except possibly at its maximum, with (1 − α)v − F̄(v)/f(v) monotone (p. 11, App-1) → Γ_α^{−1} ∘ F̄ is convex on {v ≥ 0 : F̄(v) > 0}, with no absolute-continuity requirement; reason: with h = Γ_α^{−1} ∘ F̄ the α-virtual value is (1 − α)v − (1 + (1 − α)h)/h′, which is non-decreasing exactly when h is convex; convexity on {F̄ > 0} allows exactly an atom at the top of the support (as p. 11 does) and excludes interior atoms and singular parts. The printed 'non-increasing' (p. 11) is a slip for non-decreasing (App. A; proof of Lemma C-1)
--   - encoding: sup and inf in R(Ψ, F), opt(F) and R(P′, 𝓕) → sSup and sInf on ℝ; reason: every set involved is nonempty and bounded (ratios lie in [0, 1], revenues are bounded by the mean), so the real sSup and sInf are the paper's sup and inf; no junk value arises
--   - reading: 'the optimal price is given by p*_d(w, q)' → p*_d(w, q) ≥ 0 and inf_{F ∈ F_α(w,q)} R(δ_{p*_d}, F) = R(P_d, F_α(w, q)); reason: δ_{p*_d} attains the supremum defining the maximin ratio; the page claims optimality, not uniqueness, of the price
--   - reading: w and q: an observed price and conversion rate → hypotheses 0 < w and q ∈ (0, 1); reason: standing assumptions: w is a posted price, and I ∩ {0, 1} = ∅ throughout (p. 11)
--   - encoding: q̂ 'the unique solution in [0, 1]' of W(1/log(q^{−1}))W(e/q) = 1 (undefined at q ∈ {0, 1}) → ∃! over [0, 1] with Lean's log(0⁻¹) = 0 and 1/0 = 0; reason: at q ∈ {0, 1} the product is W(0)·W(·) = 0 ≠ 1, so the endpoints are not solutions under either reading; the bound q̂ ∈ [0.52, 0.53] and the mhr formulas are stated for every solution, hence for the unique one
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Theorem 2, pp. 21–22

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det

open MeasureTheory

/-- Theorem 2 (Maximin Ratio for deterministic mechanisms), pp. 21–22. With `P_d` the
deterministic prices: for regular laws (`α = 0`) and for mhr laws (`α = 1`), every `w > 0` and
`q ∈ (0, 1)`, the maximin ratio `R(P_d, F_α(w, q))` equals the printed piecewise closed form and the
printed price `p*_d(w, q) ≥ 0` attains it (its worst-case ratio over `F_α(w, q)` equals the maximin
ratio); `q̂` is the unique solution in `[0, 1]` of `W(1/log(q^{−1})) W(e/q) = 1` and lies in
`[0.52, 0.53]`. -/
theorem theorem_2 :
    (∀ w q : ℝ, 0 < w → q ∈ Set.Ioo (0 : ℝ) 1 →
      maximin Pd (FClass 0 w q) =
          2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
          + (3 - 4 * q) / (4 * (1 - q)) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
          + (1 - q) * (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q ∧
      0 ≤ w * (2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
          + q * (3 - 4 * q) / (1 - q) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
          + (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q) ∧
      sInf (ratio (Measure.dirac
          (w * (2 * Real.sqrt q / (1 + Real.sqrt q) * (Set.Ioc (0 : ℝ) (1 / 4)).indicator 1 q
            + q * (3 - 4 * q) / (1 - q) * (Set.Ioc (1 / 4 : ℝ) (1 / 2)).indicator 1 q
            + (Set.Ioo (1 / 2 : ℝ) 1).indicator 1 q))) '' FClass 0 w q) =
        maximin Pd (FClass 0 w q)) ∧
    (∃! qh : ℝ, qh ∈ Set.Icc 0 1 ∧
      lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1) ∧
    (∀ qh : ℝ, qh ∈ Set.Icc 0 1 →
      lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1 →
      qh ∈ Set.Icc (0.52 : ℝ) 0.53 ∧
      ∀ w q : ℝ, 0 < w → q ∈ Set.Ioo (0 : ℝ) 1 →
        maximin Pd (FClass 1 w q) =
            betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
            + rhoQ q * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
            + Real.exp 1 * q * Real.log q⁻¹ * (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q ∧
        0 ≤ w * (betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
            + betaQ q (1 / Real.log q⁻¹) * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
            + (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q) ∧
        sInf (ratio (Measure.dirac
            (w * (betaQ q (Real.exp 1 / q) * (Set.Ioc 0 qh).indicator 1 q
              + betaQ q (1 / Real.log q⁻¹) * (Set.Ioc qh (Real.exp (-Real.exp (-1)))).indicator 1 q
              + (Set.Ioo (Real.exp (-Real.exp (-1))) 1).indicator 1 q))) '' FClass 1 w q) =
          maximin Pd (FClass 1 w q)) := by sorry

end SinglePointPricing.Det
