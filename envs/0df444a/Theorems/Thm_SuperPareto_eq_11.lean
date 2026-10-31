-- Prove2me | Theorems.Thm_SuperPareto_eq_11
-- name    : SuperPareto.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:27.497818+00:00
-- url     : https://prove2.me/theorems/d2347d5f-fd1c-4c78-a348-d158513fecb2
-- title:
--   Display (11), p.10 — $X\mathbb 1_B\le_{\mathrm{st}}\sum c_iX\mathbb 1_{B_i}$ for mutually exclusive events
-- statement:
--   Let $X$ be a regular super-Pareto random variable, $B_1,\dots,B_m$ mutually exclusive events, each independent of $X$, and $(c_1,\dots,c_m)\in[0,1]^m$. If $B$ is an event independent of $X$ with $P(B)=\sum_kc_kP(B_k)$, then
--
--   $$
--   X\mathbb 1_B\le_{\mathrm{st}}\sum_{k=1}^mc_kX\mathbb 1_{B_k}. \tag{11}
--   $$
--
--   In step (d) this is applied to the events $B_S$, $S\subseteq[n]$, with weights $c_S=\sum_{i\in S}\theta_i$, and gives the final comparison $\sum_S c_SX\mathbb 1_{B_S}\ge_{\mathrm{st}}X\mathbb 1_A$ in the proof of Theorem 1(ii).
--
--   **Formalization Note** The events are indexed by an arbitrary finite type. "Independent of $X$" is `IndepFun` of the event's indicator and $X$, for each event separately. $\le_{\mathrm{st}}$ is the platform definition `StarShapedRisk.LawInvariant.FSD`; $X\mathbb 1_B$ is `B.indicator X`.
--
--   Differences from the source:
--   - reading: mutually exclusive events B₁, …, Bₙ independent of X → each B_k separately independent of X (`IndepFun` of its indicator and X); reason: the proof uses only P(B_k ∩ {c_k X > t}) = P(B_k) P(c_k X > t); separate independence is implied by joint independence, so this is the weaker hypothesis and covers both readings
--   - generalization: n ≥ 2 events on an atomless probability space (standing assumptions, p.4) → events indexed by any finite type κ (any size, empty included) on any probability space; reason: the paper's case is a special case, and step (d) applies (11) to the family indexed by the subsets S ⊆ [n]; for empty κ, P(B) = 0 and both sides vanish a.s.
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (d), display (11), p.10

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_VaR
import Definitions.Def_SuperPareto_IsRegularSuperPareto

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Display (11): dominance over mutually exclusive events.** Chen, Embrechts, Wang, *An
unexpected stochastic dominance*, arXiv:2208.08471v4, §2.3, step (d), display (11), p.10: for a
regular super-Pareto `X`, mutually exclusive events `B₁, …, Bₙ` independent of `X` and
`(c₁, …, cₙ) ∈ [0, 1]ⁿ`,
`X 𝟙_B ≤st ∑ cᵢ X 𝟙_{Bᵢ}`  (11),
where `B` is an event independent of `X` satisfying `P(B) = ∑ cᵢ P(Bᵢ)`.

**Formalization Note.** The index set is an arbitrary `Fintype` `κ` (step (d) applies (11) to the
family indexed by the subsets `S ⊆ [n]`). "Independent of `X`" is, for each event separately,
`IndepFun` of its indicator and `X`. `X ≤st Z` is `StarShapedRisk.LawInvariant.FSD P X Z`.
`X 𝟙_B` is `B.indicator X`. -/
theorem eq_11 {Ω κ : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype κ] (X : Ω → ℝ) (hX : Measurable X) (hreg : IsRegularSuperPareto P X)
    (B : κ → Set Ω) (hBmeas : ∀ k, MeasurableSet (B k))
    (hBdisj : Pairwise (fun k l => Disjoint (B k) (B l)))
    (hBind : ∀ k, IndepFun ((B k).indicator (fun _ => (1 : ℝ))) X P)
    (c : κ → ℝ) (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1)
    (B₀ : Set Ω) (hB₀meas : MeasurableSet B₀)
    (hB₀ind : IndepFun (B₀.indicator (fun _ => (1 : ℝ))) X P)
    (hB₀ : P.real B₀ = ∑ k, c k * P.real (B k)) :
    StarShapedRisk.LawInvariant.FSD P (B₀.indicator X)
      (fun ω => ∑ k, c k * (B k).indicator X ω) := by sorry

end SuperPareto
