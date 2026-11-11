-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_3_B_4
-- name    : PrivInfoHier.Main.eq_B_3_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:55.962129+00:00
-- url     : https://prove2.me/theorems/62d4e1c3-1eb1-4bfa-bf9e-73e9bcdfae18
-- title:
--   §B.1, Eqs. (B.3)–(B.4) — lower-bound chain for $U_\delta(T_M)$, as printed
-- statement:
--   Let $\theta,\delta\in(0,1)$ and let $T_M$ be the App. B.1 mechanism-level filter. The δ-clipped mean of $T_M$ does not depend on the database or the request strategy, and the paper bounds it by the chain
--   $$U_\delta(T_M)=\frac1{1-\delta}\int_0^{1-\delta}Q_{T_M}(u)\,du\ \ge\ \frac{1-\delta-\delta\log\frac1\delta}{(1-\delta)\log\frac1{1-\theta}}\ \ge\ \frac{1-\delta-\frac1e}{\log\frac1{1-\theta}}\ \overset{(B.3)}{}\ \ge\ \frac{1-\theta}{\theta}\Big(\frac{e-1}e-\delta\Big)\ \overset{(B.4)}{}\ \ge\ \frac1\theta\,\frac{e-1}e-\frac\delta\theta-1.$$
--   The statement is the conjunction of all five relations: the equality for every database $x$ and strategy $\mathcal A$, and each of the four inequalities, for all $\theta,\delta\in(0,1)$. The last bound is the lower bound of Theorem 3.2(a).
--
--   As printed, step (B.4) is false for $\delta>1-1/e$ (for $\delta=0.9$, $\theta=0.5$: $-0.3865<-0.2679$), so this conjunction is false; it is posed as printed and the finding is recorded separately.
--
--   Differences from the source:
--   - generalization: fixed requests → every request space and every request strategy; reason: the B.1 rules ignore requests; App. B says the arguments hold uniformly over the strategy.
--   - reading: "$U_\delta(T_M)=\frac1{1-\delta}\int_0^{1-\delta}Q_{T_M}$" with the $x$-dependence dropped (footnote 4) → $U_\delta(T_M)$ (infimum over every database and strategy) equals the clipped integral under every database $x$ and strategy $\mathcal A$; reason: footnote 4.
--   - encoding: $U_\delta$ and the integral → values in $[0,\infty]$ (lower Lebesgue integral over $(0,1-\delta]$), the first real bound compared through `ENNReal.ofReal`; reason: $U_\delta\ge0$ and the bound is $\ge0$, so nothing changes.
--   - encoding: $T_M=+\infty$ on a null event → $0$ there; reason: ℕ-valued; probability-$0$ event.
--   - encoding: a filter on $\Omega=\mathcal Z\times(\mathcal R\times\mathcal Y)^{\mathbb N}$ under $\mathrm{law}(Z)\otimes P_{x,\mathcal A}$ → $T_M$ a function of the interaction path alone, its law under $P_{x,\mathcal A}$; reason: $T_M$ uses no internal randomness (a deterministic filter, p. 7), so its law is the same on either space.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 18 (PDF 20), App. B.1, Eqs. (B.3)–(B.4)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, (B.3)–(B.4), as printed: the chain bounding the δ-clipped mean of the B.1
mechanism-level filter `T_M` from below:
`U_δ(T_M) = (1/(1−δ)) ∫_0^{1−δ} Q_{T_M} ≥ (1 − δ − δ log(1/δ))/((1 − δ) log(1/(1 − θ)))`
`≥ (1 − δ − 1/e)/log(1/(1 − θ)) ≥ ((1 − θ)/θ)((e − 1)/e − δ) ≥ (1/θ)(e − 1)/e − δ/θ − 1`. -/
theorem eq_B_3_B_4 (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ (x : 𝒳) (A : RequestStrategy ℛ (B1Out 𝒳)),
      clippedMean (fun i : 𝒳 × RequestStrategy ℛ (B1Out 𝒳) => interLaw (b1Process 𝒳 ℛ θ) i.2 i.1)
          (TM 𝒳 ℛ θ) δ
        = ENNReal.ofReal (1 / (1 - δ)) *
            ∫⁻ u in Set.Ioc 0 (1 - δ), quantile (interLaw (b1Process 𝒳 ℛ θ) A x) (TM 𝒳 ℛ θ) u) ∧
    ENNReal.ofReal ((1 - δ - δ * Real.log (1 / δ)) / ((1 - δ) * Real.log (1 / (1 - θ.1))))
      ≤ clippedMean (fun i : 𝒳 × RequestStrategy ℛ (B1Out 𝒳) => interLaw (b1Process 𝒳 ℛ θ) i.2 i.1)
          (TM 𝒳 ℛ θ) δ ∧
    (1 - δ - 1 / Real.exp 1) / Real.log (1 / (1 - θ.1))
      ≤ (1 - δ - δ * Real.log (1 / δ)) / ((1 - δ) * Real.log (1 / (1 - θ.1))) ∧
    ((1 - θ.1) / θ.1) * ((Real.exp 1 - 1) / Real.exp 1 - δ)
      ≤ (1 - δ - 1 / Real.exp 1) / Real.log (1 / (1 - θ.1)) ∧
    (1 / θ.1) * ((Real.exp 1 - 1) / Real.exp 1) - δ / θ.1 - 1
      ≤ ((1 - θ.1) / θ.1) * ((Real.exp 1 - 1) / Real.exp 1 - δ) := by sorry

end PrivInfoHier.Main
