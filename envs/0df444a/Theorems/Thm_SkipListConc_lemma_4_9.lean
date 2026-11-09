-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_9
-- name    : SkipListConc.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:27.856542+00:00
-- url     : https://prove2.me/theorems/47c6cd5d-5730-4e57-b4b3-446b5eb0b11b
-- title:
--   Lemma 4.9 — weighted Bernoulli gap lemma $\mathbb E[e^{\eta C/S}]\le e^{(M_p(\eta)-1)W/S}$
-- statement:
--   Fix $0<p<1$. In the weighted Bernoulli gap model (Definition 4.8), positions $1,\dots,N$ are independently marked, each with probability at least $p$, and a sentinel position $0$ is always marked; $A_i=\min\{a\ge0: i-a\text{ is marked}\}$. Given weights $w_1,\dots,w_N\ge0$ set $C=\sum_iw_iA_i$ and $W=\sum_iw_i$, and let $M_p(\eta)=p/(1-(1-p)e^\eta)$. Let $S\ge W$ and $0<\eta<\ln\frac1{1-p}$. Then
--   $$
--   \mathbb E\Bigl[\exp\Bigl(\frac{\eta C}{S}\Bigr)\Bigr]\ \le\ \exp\Bigl(\frac{(M_p(\eta)-1)W}{S}\Bigr),
--   $$
--   and consequently, for every $u\ge0$,
--   $$
--   \Pr\Bigl[C>\frac{M_p(\eta)-1}{\eta}\,W+\frac{S}{\eta}\,u\Bigr]\ \le\ e^{-u}.
--   $$
--
--   It bounds a weighted sum of geometric gaps without a maximum over the gaps.
--
--   Differences from the source:
--   - encoding: expectation E[exp(·)] → lower Lebesgue integral ∫⁻ of ENNReal.ofReal (exp ·); reason: the integrand is nonnegative; a Bochner integral would be 0 on non-integrable functions
--   - encoding: marks → Boolean random variables mark i, independent over i ∈ {1, …, N}; reason: a mark is an event
--   - encoding: S ≥ W (S > 0 implicit in the division) → S ≥ W with Lean's x/0 = 0; reason: at S = 0 all weights vanish, C = 0, and both claims hold trivially (1 ≤ 1, Pr[0 < 0] = 0)
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 4.8 and Lemma 4.9, p.26

import Mathlib
import Definitions.Def_SkipListConc_gapLen
import Definitions.Def_SkipListConc_Mp

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 4.9 (weighted Bernoulli gap lemma) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip
Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c),
Definition 4.8 and Lemma 4.9, p.26). Positions `1, …, N` are independently marked, each with
probability at least `p`, and the sentinel `0` is always marked; `A_i` is the gap left of `i`,
`C = ∑_i w_i A_i` and `W = ∑_i w_i` for weights `w_i ≥ 0`. Let `S ≥ W` and
`0 < η < ln(1/(1 − p))`. Then
`E[exp(ηC/S)] ≤ exp((M_p(η) − 1) W / S)`, and consequently, for every `u ≥ 0`,
`Pr[C > ((M_p(η) − 1)/η) W + (S/η) u] ≤ e^{−u}`.

**Formalization Note** Marks are Boolean random variables, independent over `i ∈ {1, …, N}`. The
expectation is a lower Lebesgue integral. At `S = 0` (so `W = C = 0`) Lean's `0/0 = 0` makes both
claims read `1 ≤ 1` and `Pr[0 < 0] ≤ e^{−u}`. -/
theorem lemma_4_9 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (mark : ℕ → Ω → Bool)
    (hmeas : ∀ i, Measurable (mark i))
    (hind : iIndepFun (fun i : Finset.Icc 1 N => mark i) P)
    (hprob : ∀ i ∈ Finset.Icc 1 N, ENNReal.ofReal p ≤ P {ω | mark i ω = true})
    (w : ℕ → ℝ) (hw : ∀ i ∈ Finset.Icc 1 N, 0 ≤ w i) (S : ℝ)
    (hS : ∑ i ∈ Finset.Icc 1 N, w i ≤ S) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η < Real.log (1 / (1 - p))) :
    ∫⁻ ω, ENNReal.ofReal
        (Real.exp (η * (∑ i ∈ Finset.Icc 1 N, w i * (gapLen mark i ω : ℝ)) / S)) ∂P ≤
      ENNReal.ofReal (Real.exp ((Mp p η - 1) * (∑ i ∈ Finset.Icc 1 N, w i) / S)) ∧
    ∀ u : ℝ, 0 ≤ u →
      P {ω | (Mp p η - 1) / η * (∑ i ∈ Finset.Icc 1 N, w i) + S / η * u <
          ∑ i ∈ Finset.Icc 1 N, w i * (gapLen mark i ω : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-u)) := by sorry

end SkipListConc
