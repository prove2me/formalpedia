-- Prove2me | Theorems.Thm_TailRiskSharing_VaRConv_display15_16_partition
-- name    : TailRiskSharing.VaRConv.display15_16_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:04.008728+00:00
-- url     : https://prove2.me/theorems/eff7ee55-0a5c-4414-a2a2-e61e24346e8e
-- title:
--   (15)–(16), p. 11 — a partition with P((X − VaR^R_α(X))1_{A_i} > ε) < α_i and VaR^R_{α_i}((X − VaR^R_α(X))1_{A_i}) ≤ 0
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $n\ge1$, $\alpha_1,\dots,\alpha_n>0$ with $\alpha=\sum_{i=1}^n\alpha_i<1$, and $X$ a random variable. Then there is a partition $(A_1,\dots,A_n)$ of $\Omega$ such that for every $i=1,\dots,n$,
--
--   $$\mathbb P\big((X-\mathrm{VaR}^R_\alpha(X))\mathbb 1_{A_i}>\varepsilon\big)<\alpha_i\quad\text{for all }\varepsilon>0,\qquad(15)$$
--
--   and
--
--   $$\mathrm{VaR}^R_{\alpha_i}\big((X-\mathrm{VaR}^R_\alpha(X))\mathbb 1_{A_i}\big)\le0.\qquad(16)$$
--
--   The excess of $X$ over its right quantile at level $\alpha$ can be split into $n$ pieces each of which carries a non-positive right VaR at its own level $\alpha_i$. This is the key step of the existence part, Theorem 1(ii), in the case where some agent uses a right quantile.
--
--   **Formalization Note** The partition consists of measurable, pairwise disjoint sets covering $\Omega$; some $A_i$ may be empty. The page establishes (15) and (16) for the partition it constructs; the statement asserts that such a partition exists.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 11, proof of Theorem 1(ii), displays (15) and (16)

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory

namespace TailRiskSharing.VaRConv

theorem display15_16_partition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (n : ℕ) (hn : 1 ≤ n) (αs : Fin n → ℝ) (hα : ∀ i, 0 < αs i) (hsum : ∑ i, αs i < 1)
    (X : Ω → ℝ) (hX : X ∈ (L0 : Set (Ω → ℝ))) :
    ∃ A : Fin n → Set Ω, IsMeasPartition A ∧ ∀ i,
      (∀ ε : ℝ, 0 < ε →
        P.real {ω | ε < (X ω - VaRR P (∑ j, αs j) X) * (A i).indicator 1 ω} < αs i) ∧
      VaRR P (αs i) (fun ω => (X ω - VaRR P (∑ j, αs j) X) * (A i).indicator 1 ω) ≤ 0 := by sorry

end TailRiskSharing.VaRConv
