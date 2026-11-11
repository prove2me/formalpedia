-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_8
-- name    : PrivInfoHier.Main.eq_B_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:38.332408+00:00
-- url     : https://prove2.me/theorems/68c4819e-92d0-4c29-b3f9-86767be209e6
-- title:
--   §B.1, Eq. (B.8) — quantiles of a valid spec-level filter on the B.1 process
-- statement:
--   Let $\theta,\delta\in(0,1)$, $\varepsilon>0$, let the database space contain a neighbouring pair $x_0\sim x_0'$ with $x_0\ne x_0'$, and consider the App. B.1 process. Let $T_S$ be an $(\varepsilon,\delta)$-valid spec-level filter. Then under every database and every request strategy, for $0\le u<1-\delta$, $\hat t:=Q_{T_S}(u)$ satisfies
--   $$\hat t\le1+\frac{\log\big(1-\frac{\delta}{1-u}\big)}{\log(1-\theta)}.$$
--
--   Differences from the source:
--   - generalization: fixed requests → every request space and every request strategy; reason: the B.1 rules ignore requests; App. B says the arguments hold uniformly.
--   - generalization: a spec-level filter with a finite horizon → any spec-level filter, no horizon assumed; reason: the argument never uses the horizon.
--   - reading: a single neighbouring pair $x\sim x'$ (p. 17) → a database space containing some $x_0\sim x_0'$ with $x_0\ne x_0'$; reason: validity must constrain the filter, which needs a pair of distinct neighbours.
--   - reading: "the quantile function" → $Q(u)=\inf\{t:P(T\le t)\ge u\}$ in $[0,\infty]$ on $u\in[0,1-\delta)$, under every database and strategy; reason: the left-continuous inverse is the one with "$P(T_S\ge\hat t)\ge1-u$ by definition"; footnote 4 drops the $x$-dependence.
--   - encoding: the bound compared through `ENNReal.ofReal`; reason: the right side is positive.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 19 (PDF 21), App. B.1, Eq. (B.8)

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model
import Definitions.Def_PrivInfoHier_Main_Filter
import Definitions.Def_PrivInfoHier_Main_B1

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivInfoHier.Main

/-- App. B.1, (B.8): on the B.1 process (database space with a neighbouring pair `x₀ ∼ x₀′`,
`x₀ ≠ x₀′`), every `(ε, δ)`-valid spec-level filter `T_S` has, under every database and every
request strategy, `Q_{T_S}(u) ≤ 1 + log(1 − δ/(1 − u))/log(1 − θ)` for `0 ≤ u < 1 − δ`. -/
theorem eq_B_8 (𝒳 ℛ : Type) [MeasurableSpace ℛ] (nb : 𝒳 → 𝒳 → Prop)
    (hnd : ∃ x₀ x₀' : 𝒳, nb x₀ x₀' ∧ x₀ ≠ x₀')
    (θ : Set.Ioo (0 : ℝ) 1) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (𝒵 : Type) [MeasurableSpace 𝒵] (μZ : Measure 𝒵) [IsProbabilityMeasure μZ]
    (T : 𝒵 × Path ℛ (B1Out 𝒳) → ℕ) (hspec : IsSpecLevel T)
    (hvalid : IsValid (b1Process 𝒳 ℛ θ) nb ε δ μZ T)
    (A : RequestStrategy ℛ (B1Out 𝒳)) (x : 𝒳) (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 - δ) :
    quantile (filterLaw (b1Process 𝒳 ℛ θ) A x μZ) T u
      ≤ ENNReal.ofReal (1 + Real.log (1 - δ / (1 - u)) / Real.log (1 - θ.1)) := by sorry

end PrivInfoHier.Main
