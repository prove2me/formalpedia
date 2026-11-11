-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_9
-- name    : PrivInfoHier.Main.eq_B_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:46.077553+00:00
-- url     : https://prove2.me/theorems/677be72a-6481-4ab1-82ea-5a3b2ac75c55
-- title:
--   §B.1, Eq. (B.9) — $U_\delta(T_S)\le 1+h(\delta)/(\theta(1-\delta))$ for valid spec-level filters on the B.1 process
-- statement:
--   Let $\theta,\delta\in(0,1)$, $\varepsilon>0$, let the database space contain a neighbouring pair $x_0\sim x_0'$ with $x_0\ne x_0'$, and consider the App. B.1 process. Every $(\varepsilon,\delta)$-valid spec-level filter $T_S$ satisfies
--   $$U_\delta(T_S)=\frac1{1-\delta}\int_0^{1-\delta}Q_{T_S}(u)\,du\le1+\frac1{(1-\delta)\log(1-\theta)}\int_0^{1-\delta}\log\Big(1-\frac{\delta}{1-u}\Big)du=1-\frac{h(\delta)}{(1-\delta)\log(1-\theta)}=1+\frac{h(\delta)}{(1-\delta)\log\frac1{1-\theta}}\le1+\frac{h(\delta)}{\theta(1-\delta)},$$
--   where $h(\delta)=-\delta\log\delta-(1-\delta)\log(1-\delta)$ is the binary entropy in nats. The statement is the conjunction of the five relations: the equality for every database $x$ and strategy $\mathcal A$ (the law of $T_S$ does not depend on them), and the four relations after it. The last bound is Theorem 3.2(b).
--
--   Differences from the source:
--   - generalization: fixed requests → every request space and every request strategy; reason: the B.1 rules ignore requests; App. B says the arguments hold uniformly.
--   - generalization: a spec-level filter with a finite horizon → any spec-level filter, no horizon assumed; reason: the argument never uses the horizon.
--   - reading: a single neighbouring pair (p. 17) → a database space containing some $x_0\sim x_0'$ with $x_0\ne x_0'$; reason: validity must constrain the filter.
--   - reading: "$U_\delta(T_S)=\frac1{1-\delta}\int_0^{1-\delta}Q_{T_S}$" with the $x$-dependence dropped (p. 18: the law of $T_S$ is identical under every database) → $U_\delta(T_S)$ (infimum over every database and strategy) equals the clipped integral under every database $x$ and strategy $\mathcal A$, with $Q(u)=\inf\{t:P(T\le t)\ge u\}$; reason: p. 18 and footnote 4.
--   - encoding: $U_\delta$ in $[0,\infty]$, compared with the real bound through `ENNReal.ofReal`; the integral is the interval integral of an integrable function; $h$ is `Real.binEntropy`; reason: Lean conventions, same values.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 19 (PDF 21), App. B.1, Eq. (B.9)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, (B.9): on the B.1 process (database space with a neighbouring pair `x₀ ∼ x₀′`,
`x₀ ≠ x₀′`), every `(ε, δ)`-valid spec-level filter `T_S` has
`U_δ(T_S) = (1/(1 − δ)) ∫_0^{1−δ} Q_{T_S}(u) du` under every database and request strategy, and
`U_δ(T_S) ≤ 1 + (1/((1 − δ) log(1 − θ))) ∫_0^{1−δ} log(1 − δ/(1 − u)) du = 1 − h(δ)/((1 − δ) log(1 − θ))
 = 1 + h(δ)/((1 − δ) log(1/(1 − θ))) ≤ 1 + h(δ)/(θ(1 − δ))`, `h` the binary entropy in nats. -/
theorem eq_B_9 (𝒳 ℛ : Type) [MeasurableSpace ℛ] (nb : 𝒳 → 𝒳 → Prop)
    (hnd : ∃ x₀ x₀' : 𝒳, nb x₀ x₀' ∧ x₀ ≠ x₀')
    (θ : Set.Ioo (0 : ℝ) 1) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒵 : Type) [MeasurableSpace 𝒵] (μZ : Measure 𝒵) [IsProbabilityMeasure μZ]
    (T : 𝒵 × Path ℛ (B1Out 𝒳) → ℕ) (hspec : IsSpecLevel T)
    (hvalid : IsValid (b1Process 𝒳 ℛ θ) nb ε δ μZ T) :
    (∀ (x : 𝒳) (A : RequestStrategy ℛ (B1Out 𝒳)),
      filterClippedMean (b1Process 𝒳 ℛ θ) μZ T δ
        = ENNReal.ofReal (1 / (1 - δ)) *
            ∫⁻ u in Set.Ioc 0 (1 - δ), quantile (filterLaw (b1Process 𝒳 ℛ θ) A x μZ) T u) ∧
    filterClippedMean (b1Process 𝒳 ℛ θ) μZ T δ
      ≤ ENNReal.ofReal (1 + (1 / ((1 - δ) * Real.log (1 - θ.1))) *
          ∫ u in (0 : ℝ)..(1 - δ), Real.log (1 - δ / (1 - u))) ∧
    1 + (1 / ((1 - δ) * Real.log (1 - θ.1))) * ∫ u in (0 : ℝ)..(1 - δ), Real.log (1 - δ / (1 - u))
      = 1 - Real.binEntropy δ / ((1 - δ) * Real.log (1 - θ.1)) ∧
    1 - Real.binEntropy δ / ((1 - δ) * Real.log (1 - θ.1))
      = 1 + Real.binEntropy δ / ((1 - δ) * Real.log (1 / (1 - θ.1))) ∧
    1 + Real.binEntropy δ / ((1 - δ) * Real.log (1 / (1 - θ.1)))
      ≤ 1 + Real.binEntropy δ / (θ.1 * (1 - δ)) := by sorry

end PrivInfoHier.Main
