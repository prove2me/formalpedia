-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_A_1
-- name    : RecruitSmaller.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:09:47.815245+00:00
-- url     : https://prove2.me/theorems/4ee64036-51eb-421f-a6a1-c3008d910832
-- title:
--   Lemma A.1 — quantile coupling of the buyer order statistics
-- statement:
--   Let $U_1,\dots,U_m$ be i.i.d. Uniform$(0,1)$ with sorted order statistics $U^{(1)}\ge\cdots\ge U^{(m)}$, let $W_{i,m}:=1-U^{(i)}$, and let $F_B^{-1}(u)=\inf\{z:F_B(z)\ge u\}$ be the generalized inverse of the buyer CDF. Then:
--
--   1. (o) $W_{i,m}$ has the Beta$(i,m-i+1)$ density $f_{i,m}$ on $(0,1)$, for each $i\in\{1,\dots,m\}$;
--   2. (i) the vector $\bigl(F_B^{-1}(U^{(1)}),\dots,F_B^{-1}(U^{(m)})\bigr)$ has the exact joint distribution of the sorted buyer valuations $(b^{(1)},\dots,b^{(m)})$ with $b_j$ i.i.d. $F_B$;
--   3. (ii) for any threshold $x\in\mathbb R$, with $q_x:=F_B(x-)\in[0,1]$, for all $u\in(0,1)$,
--   $$
--   u>q_x\ \Longrightarrow\ F_B^{-1}(u)\ge x\ \Longrightarrow\ u\ge q_x; \tag{A.3}
--   $$
--   4. consequently, for every $x$ and every rank $i$, $\mathbb 1[F_B^{-1}(U^{(i)})\ge x]=\mathbb 1[W_{i,m}<1-q_x]$ almost surely.
--
--   No continuity of $F_B$ is assumed: the lemma is what lets the paper treat distributions with atoms and flat parts.
--
--   **Formalization Note** $F_B^{-1}$ is the published generalized inverse `ResAllocGaps.quantile`; $q_x=\mu_B((-\infty,x))$. The joint law of $U$ is the product of Lebesgue measure on $(0,1)$.
--
--   Differences from the source:
--   - reading: “let W_{i,m} := 1 − U⁽ⁱ⁾ ∼ Beta(i, m − i + 1) have density f_{i,m}(w)” in the lemma's preamble (cited to [21]) → clause (o): the law of 1 − U⁽ⁱ⁾ is f_{i,m} times Lebesgue measure on (0, 1), for each i ∈ {1, …, m}; reason: the page asserts it inside the lemma and Lemma 3.8 uses it; stated as a claim rather than left implicit
--   - encoding: q_x := F_B(x−) → (μB (Iio x)).toReal; reason: F_B(x−) = μB((−∞, x)) for a probability measure; same value
--   - encoding: equality of indicators almost surely → equivalence of the two events almost surely; reason: 𝟙[P] = 𝟙[Q] iff (P ↔ Q)
--   - encoding: U₁, …, U_m i.i.d. Uniform(0, 1) → the product of m copies of Lebesgue measure restricted to (0, 1); reason: that is the Uniform(0, 1)ᵐ law
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma A.1, p.26

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_betaDens
import Definitions.Def_RecruitSmaller_unifCube
import Definitions.Def_ResAllocGaps_quantile

open MeasureTheory

namespace RecruitSmaller

/-- **Lemma A.1** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.26): let `U₁, …, U_m` be i.i.d. Uniform(0, 1) with
sorted order statistics `U⁽¹⁾ ≥ ⋯ ≥ U⁽ᵐ⁾`, and `W_{i,m} := 1 − U⁽ⁱ⁾`. Then
(o) `W_{i,m}` has the Beta(i, m − i + 1) density `f_{i,m}` on `(0, 1)`;
(i) `(F_B⁻¹(U⁽¹⁾), …, F_B⁻¹(U⁽ᵐ⁾))` has the joint distribution of the sorted buyer values
`(b⁽¹⁾, …, b⁽ᵐ⁾)`;
(ii) for every `x ∈ ℝ`, with `q_x := F_B(x−)`, for all `u ∈ (0, 1)`:
`u > q_x ⇒ F_B⁻¹(u) ≥ x ⇒ u ≥ q_x` (A.3); and consequently
`𝟙[F_B⁻¹(U⁽ⁱ⁾) ≥ x] = 𝟙[W_{i,m} < 1 − q_x]` almost surely.

**Formalization Note** `F_B⁻¹` is the published generalized inverse `ResAllocGaps.quantile`
(`inf {z : u ≤ F_B(z)}`); `q_x = F_B(x−) = μB((−∞, x))`. The page asserts the Beta law of
`W_{i,m}` in the lemma's preamble; it is stated here as clause (o). The almost-sure clause is stated
for each rank `i ∈ {1, …, m}`. -/
theorem lemma_A_1 (m : ℕ) (μB : Measure ℝ) [IsProbabilityMeasure μB] :
    (∀ i : ℕ, 1 ≤ i → i ≤ m →
      (unifCube m).map (fun U : Fin m → ℝ => 1 - buyerOrd U i) =
        ((volume : Measure ℝ).restrict (Set.Ioo 0 1)).withDensity
          (fun w => ENNReal.ofReal (betaDens m i w))) ∧
    (unifCube m).map (fun U : Fin m → ℝ => fun j : Fin m =>
        ResAllocGaps.quantile μB (buyerOrd U (j.val + 1))) =
      (Measure.pi fun _ : Fin m => μB).map (fun b : Fin m → ℝ => fun j : Fin m =>
        buyerOrd b (j.val + 1)) ∧
    (∀ x u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      ((μB (Set.Iio x)).toReal < u → x ≤ ResAllocGaps.quantile μB u) ∧
      (x ≤ ResAllocGaps.quantile μB u → (μB (Set.Iio x)).toReal ≤ u)) ∧
    (∀ x : ℝ, ∀ i : ℕ, 1 ≤ i → i ≤ m →
      ∀ᵐ U ∂(unifCube m), (x ≤ ResAllocGaps.quantile μB (buyerOrd U i) ↔
        1 - buyerOrd U i < 1 - (μB (Set.Iio x)).toReal)) := by sorry

end RecruitSmaller
