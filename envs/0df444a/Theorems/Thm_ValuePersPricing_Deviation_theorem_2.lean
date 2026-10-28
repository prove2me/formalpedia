-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_theorem_2
-- name    : ValuePersPricing.Deviation.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:01.27399+00:00
-- url     : https://prove2.me/theorems/6c239a16-0787-43d0-b269-8d732faae038
-- title:
--   Theorem 2, p. 13 — R_PP/R_SP is at most the low/medium/high-heterogeneity bound in S, M, D, and each bound is tight (corrected: for D > 0)
-- statement:
--   Let $(F,c)$ be a market: a valuation $V\sim F$ with $V\ge c\ge 0$ almost surely and finite mean $\mu>c$, so that the margin $M=1-c/\mu$ lies in $(0,1]$. Let $D=\mathbb E|V-\mu|/(2\mu)$ be the coefficient of deviation and, for a scale $S$, write $\delta_L,\delta_M,\delta_H$ for the thresholds of §3.2 at $(M,S)$.
--
--   **Upper bounds.** If $F$ has scale $S>1$, then
--
--   1. if $0\le D\le\delta_L$,
--   $$\frac{\mathcal R_{PP}(F,c)}{\mathcal R_{SP}(F,c)}\le\frac{-W_{-1}\big(\frac{D/M-1}{e}\big)}{1-\frac DM}\qquad\text{(Low Heterogeneity)};$$
--   2. if $\delta_L\le D\le\delta_M$,
--   $$\frac{\mathcal R_{PP}(F,c)}{\mathcal R_{SP}(F,c)}\le\frac{M\log\big(\frac{S+M-1}{M}\big)}{D}\qquad\text{(Medium Heterogeneity)};$$
--   3. if $\delta_M\le D\le\delta_H$,
--   $$\frac{\mathcal R_{PP}(F,c)}{\mathcal R_{SP}(F,c)}\le -W_{-1}\Big(\frac{-1}{e\,\frac{S+M-1}{M}\,(1-\frac DM)}\Big)\qquad\text{(High Heterogeneity)}.$$
--
--   If $F$ has unbounded support ($S=\infty$), the Low Heterogeneity bound holds for every $D$.
--
--   **Tightness.** For every mean $\mu$, cost $c$ with $0\le c<\mu$, scale $S>1$ and $D>0$, writing $M=1-c/\mu$: in each regime that contains $D$ (on its closed interval), there is a valuation law with mean $\mu$, scale $S$ and coefficient of deviation $D$ for which that regime's bound holds with equality.
--
--   The theorem gives a closed-form, tight upper bound on the value of idealized personalized pricing over single pricing from three summary statistics of the valuation distribution; equivalently, the reciprocal of the bound is a tight guarantee on the share of the personalized-pricing profit that one optimal posted price earns.
--
--   **Formalization Note** Ratios are stated multiplicatively, $\mathcal R_{PP}\le B\,\mathcal R_{SP}$. $\mathcal R_{SP}$ is a supremum over all real prices and is not assumed attained or positive.
--
--   Differences from the source:
--   - correction: "for any S, M, D there exists a valuation distribution F … such that the corresponding bound is tight" → for every D > 0 in the regime's closed interval; reason: S = 2, c = 0, µ = 1, D = 0 meets every printed assumption, but D = 0 forces V = µ almost surely, whose scale is 1, so no such law exists.
--   - reading: "For any F with scale S > 1" → S ∈ (1, ∞) plus a separate clause for unbounded support (S = ∞) with the Low Heterogeneity bound; reason: p. 8 says S may be infinite and all bounds remain valid, and p. 13 says that for S = ∞ the low heterogeneity bound always pertains.
--   - generalization: "there exists F with scale S, margin M and coefficient of deviation D" → for every mean µ and cost c with 0 ≤ c < µ (hence every M ∈ (0,1]) a law with mean µ, cost c, scale S and deviation D; reason: the proof on p. ec3 constructs it "given S, M, D, and µ"; choosing any µ, c with 1 − c/µ = M gives the printed claim.
--   - encoding: R_PP/R_SP ≤ B and "tight" → R_PP ≤ B·R_SP and R_PP = B·R_SP; reason: R_SP > 0 under the hypotheses, and the product form cannot hold vacuously through a zero denominator.
--   - encoding: a nonnegative random variable V ∼ F with V ≥ c a.s. → a probability measure ν on ℝ with Market ν c (0 ≤ c, V ≥ c a.s., E|V| < ∞); reason: standing assumptions of §2.
--   - encoding: S := inf{k | F(k) = 1}/µ → the predicate IsScale ν S (Sµ is the essential supremum of V); reason: the same quantity, without an extended-real infimum.
--   - encoding: W₋₁ → lambertWm1, defined by choice with the junk value 0 off [−1/e, 0); reason: every argument of W₋₁ in the statement lies in [−1/e, 0) under its hypotheses.
--   - encoding: margin M > 0 and 0 ≤ D → hypothesis c < µ, and no hypothesis 0 ≤ D; reason: M > 0 ⇔ c < µ, and D ≥ 0 holds for every law.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. 13 (PDF 13), Theorem 2; regimes p. 12 (PDF 12); S = ∞: pp. 8, 13; proof App. B.2–B.3, pp. ec2–ec9 (PDF 34–41)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Theorem 2 (Elmachtoub–Gupta–Hamilton, p. 13): the three-regime upper bound on `R_PP / R_SP` in
terms of scale `S`, margin `M` and coefficient of deviation `D`, stated multiplicatively, with the
unbounded-support case (`S = ∞`, pp. 8 and 13), and tightness of each regime's bound on its closed
interval for every `D > 0` (corrected: at `D = 0` no law has scale `S > 1`). -/
theorem theorem_2 :
    (∀ (ν : Measure ℝ) (c : ℝ), Market ν c → c < mean ν →
      (∀ S : ℝ, 1 < S → IsScale ν S →
        (coefDev ν ≤ deltaL (margin ν c) S →
          ppProfit ν c ≤ lowBound (margin ν c) (coefDev ν) * spProfit ν c) ∧
        (deltaL (margin ν c) S ≤ coefDev ν → coefDev ν ≤ deltaM (margin ν c) S →
          ppProfit ν c ≤ medBound (margin ν c) S (coefDev ν) * spProfit ν c) ∧
        (deltaM (margin ν c) S ≤ coefDev ν → coefDev ν ≤ deltaH (margin ν c) S →
          ppProfit ν c ≤ highBound (margin ν c) S (coefDev ν) * spProfit ν c)) ∧
      (Unbounded ν →
        ppProfit ν c ≤ lowBound (margin ν c) (coefDev ν) * spProfit ν c)) ∧
    (∀ μ c S D : ℝ, 0 ≤ c → c < μ → 1 < S → 0 < D →
      (D ≤ deltaL (1 - c / μ) S →
        ∃ ν : Measure ℝ, Market ν c ∧ mean ν = μ ∧ IsScale ν S ∧ coefDev ν = D ∧
          ppProfit ν c = lowBound (1 - c / μ) D * spProfit ν c) ∧
      (deltaL (1 - c / μ) S ≤ D → D ≤ deltaM (1 - c / μ) S →
        ∃ ν : Measure ℝ, Market ν c ∧ mean ν = μ ∧ IsScale ν S ∧ coefDev ν = D ∧
          ppProfit ν c = medBound (1 - c / μ) S D * spProfit ν c) ∧
      (deltaM (1 - c / μ) S ≤ D → D ≤ deltaH (1 - c / μ) S →
        ∃ ν : Measure ℝ, Market ν c ∧ mean ν = μ ∧ IsScale ν S ∧ coefDev ν = D ∧
          ppProfit ν c = highBound (1 - c / μ) S D * spProfit ν c)) := by sorry

end ValuePersPricing.Deviation
