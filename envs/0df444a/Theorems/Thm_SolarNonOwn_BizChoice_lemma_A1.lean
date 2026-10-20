-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_lemma_A1
-- name    : SolarNonOwn.BizChoice.lemma_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:04.071959+00:00
-- url     : https://prove2.me/theorems/59366689-40c8-414b-aca2-15b984afbf6a
-- title:
--   Lemma A.1, p. OA1 — sales-only profitability and appendix closed forms
-- statement:
--   When the company can sell panels but cannot lease them or offer a PPA, a positive profit is possible only below the critical panel cost
--
--   $$C_0(\alpha,\beta,r)=\frac{g(r+\beta)}{1-\alpha}.$$
--
--   For $0\le c<C_0$, the proof's price $s_0^*=[g(r+\beta)+c(1-\alpha)]/[2(1-\alpha)]$ attains the maximum sales-only profit $\Pi_0^*=[g(r+\beta)-c(1-\alpha)]^2/[4g(1-\alpha)(r+\beta)]>0$. The threshold $C_0$ increases strictly in $\alpha$, $\beta$ and $r$ within their indicated nonnegative ranges.
--
--   This benchmark supplies both the paper's restriction $c<C_0$ and the value of Case B1.
--
--   **Formalization Note** The theorem includes the closed forms established in the proof on p. OA3 as well as the printed Lemma A.1. Its parameter hypotheses are the §3 model assumptions $\alpha,\beta>0$, $0<t<r$, $g>0$, plus $\alpha<1$, the meaning of “$\alpha$ fraction of the investment cost” (p. 8); the p. 15 conditions $\beta<r$ and $\alpha<A$ are not assumed.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. OA1 (PDF p. 33), Lemma A.1; p. OA3 (PDF p. 35), proof

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

/-- Lemma A.1, p. OA1, including the optimum calculated in its proof, p. OA3.
The final three clauses state its claim that C0 increases in each of α, β, r.
`α < 1` is the reading of "α fraction of the investment cost" (p. 8). -/
theorem lemma_A1 (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hh : h (Set.Iic 0) = 0) (hs : ModelAssumptions prm) (hα1 : prm.alpha < 1) :
    (∀ c s : ℝ, 0 < profit0 prm h c s → c < C0 prm) ∧
    (∀ c : ℝ, 0 ≤ c → c < C0 prm →
      0 < profit0 prm h c (s0star prm c) ∧
      profit0 prm h c (s0star prm c) = prof0star prm c ∧
      ∀ s : ℝ, profit0 prm h c s ≤ prof0star prm c) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b → b < 1 →
      C0 {prm with alpha := a} < C0 {prm with alpha := b}) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b →
      C0 {prm with beta := a} < C0 {prm with beta := b}) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b →
      C0 {prm with r := a} < C0 {prm with r := b}) := by sorry

end SolarNonOwn.BizChoice
