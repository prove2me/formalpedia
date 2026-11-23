-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_theorem_4
-- name    : SPPRevenue.SingleUnit.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:19:22.871505+00:00
-- url     : https://prove2.me/theorems/1dddd9bf-da58-4fc6-91f1-bd1e3c737f6e
-- title:
--   Theorem 4 (corrected: 0.6543 ≤ 1/FR-Multi(1)) — the n²-price SPP position auction earns Σ_j f_j/FR-Multi(j) of the optimal revenue
-- statement:
--   Consider the position auction with click-through rates $1\ge\alpha_1\ge\dots\ge\alpha_n\ge0$, $\alpha_{n+1}=0$, and $n\ge1$ buyers with independent values $v_i\sim\mu_i$. For each $j\in[n]$ let $M^j$ be an optimal truthful, individually rational $j$-unit mechanism with 0/1 allocations, nonnegative payments and revenue $\mathrm{Opt}_j$. Let $t^j$ be measurable nonnegative own-value-independent thresholds satisfying the $j$-unit capacity bound almost surely. Write $B_j$ for their expected threshold revenue, and assume $\mathrm{Opt}_j\le B_j$. Let $\mathrm{Opt}_{PA}$ be the revenue of the position-auction mechanism of Lemma 6 built from them, so $\mathrm{Opt}_{PA}=\sum_j(\alpha_j-\alpha_{j+1})\mathrm{Opt}_j$, and (Equation (9))
--   $$f_j=\frac{(\alpha_j-\alpha_{j+1})\,\mathrm{Opt}_j}{\mathrm{Opt}_{PA}}.$$
--   Assume $B_j$ is finite whenever $\alpha_j-\alpha_{j+1}>0$; components with zero click gaps need no revenue restriction. Let the SPP mechanism for position auctions run, for each $j$, the $j$-unit SPP mechanism with the best of the Myersonian and uniform prices, selling $\alpha_j-\alpha_{j+1}$ clicks (Equation (10)); its revenue envelope is $\sum_j(\alpha_j-\alpha_{j+1})\max(\mathrm{MP}_j,\mathrm{UP}_j)$. Then:
--
--   1. the mechanism of Lemma 6 is optimal among truthful, individually rational position-auction mechanisms;
--   2. the SPP revenue envelope is at least $\sum_j(\alpha_j-\alpha_{j+1})\,B_j/\mathrm{FR\text{-}Multi}(j)$;
--   3. there are nonnegative prices $p^j_i$, each $p^j$ either a uniform price vector or a realization of the re-sampled thresholds of $t^j$, whose deterministic $n^2$-price SPP mechanism allocates feasible expected clicks (a randomized position allocation and inequalities (8)) at every value profile, is truthful and individually rational, and earns at least the same weighted approximation amount;
--   4. $0.6543\le1/\mathrm{FR\text{-}Multi}(1)$;
--   5. if $\mathrm{Opt}_{PA}>0$, then $\sum_jf_j=1$ and
--   $$\text{SPP revenue}\ \ge\ \Big(\sum_{j\in[n]}\frac{f_j}{\mathrm{FR\text{-}Multi}(j)}\Big)\mathrm{Opt}_{PA},\qquad \sum_{j\in[n]}\frac{f_j}{\mathrm{FR\text{-}Multi}(j)}\ \ge\ \frac1{\mathrm{FR\text{-}Multi}(1)}.$$
--
--   So the SPP mechanism for position auctions is a $\sum_jf_j/\mathrm{FR\text{-}Multi}(j)$-approximation, which is at least $1/\mathrm{FR\text{-}Multi}(1)\ge0.6543$.
--
--   **Formalization Note** $\mathrm{MP}_j$ averages over the random Myersonian prices and $\mathrm{UP}_j$ is a supremum over uniform prices, which need not be attained; item 3 gives deterministic prices. Benchmark revenues are signed extended expectations with no undefined difference of infinities; the nonnegative aggregate PA revenue is finite under the positive-gap hypotheses; the SPP revenues and the fractions $f_j$ are in $[0,\infty]$. Item 2 holds without dividing by $\mathrm{Opt}_{PA}$, which covers $\mathrm{Opt}_{PA}=0$.
--
--   Differences from the source:
--   - reading: Opt_PA, the optimal revenue of the PA setting, and the j-unit optimal mechanisms → actual optimal j-unit mechanisms M j with pointwise feasible allocations; hbenchmark requires their revenues to be at most the feasible threshold revenues B_j; Opt_PA and f_j use the actual M revenues, and paMech α M is proved optimal; reason: pp. 10–11 allow losing-tie thresholds to be raised. This preserves allocations on finite supports but can increase payments, so revenue domination is sufficient and exact payment agreement is unnecessary. For atomless laws, ordinary thresholds agree almost surely. Equation (9) uses actual optimal revenues, not the possibly increased threshold benchmark
--   - generalization: the j-unit optimal mechanisms are Myerson's, for atomless or finitely supported laws → any family of optimal j-unit mechanisms with 0/1 allocations and nonnegative payments, and any feasible threshold benchmarks whose finite positive-gap revenues dominate theirs, for arbitrary value laws; reason: source atomless thresholds give equality almost surely; the finite-support construction in footnote 5 gives domination and finite revenues. The full weighted guarantee follows with the source optimal revenues. Nesting is not needed for the randomized expected-click allocation (Lemma 7)
--   - reading: our SPP mechanism, with the best of Myersonian and uniform prices for every j → the envelope Σ_j (α_j − α_{j+1}) max(MP_j, UP_j), plus deterministic n² prices (each p^j uniform or a realization of the re-sampled thresholds) with realizable feasible clicks, truthfulness, individual rationality and at least the weighted approximation guarantee; reason: UP_j is a supremum that may be unattained. The deterministic conclusion achieves the approximation target; it does not claim to attain the envelope
--   - correction: 1/FR-Multi(1) = 0.6543 → 6543/10000 ≤ (frMulti 1)⁻¹; reason: FR-Multi(1) = FR = 1 + ln τ⋆ = 1.52810 (published fr_value), so 1/FR-Multi(1) = 0.65440, which does not round to 0.6543; the inequality is what the approximation claim needs
--   - reading: Σ_j f_j/FR-Multi(j) of the optimal revenue, f_j from Equation (9) → the ratio statement under 0 < Opt_PA, with Σ f_j = 1; the stronger undivided bound uses the dominating B_j, and holds also at Opt_PA = 0; reason: Equation (9) divides actual weighted optimal revenues by Opt_PA. These are bounded by the threshold revenues B_j, so the undivided B_j bound implies the full source approximation and covers zero without division
--   - encoding: positions j ∈ [n], α_{n+1} = 0, 1 ≤ n → Fin n indices shifted by one, ctrGap, 1 ≤ n; reason: Lean indexing; same instances
--   - correction: no explicit finiteness assumption on optimal PA revenue → hfin: optRev μ (t j) ≠ ⊤ whenever ctrGap α j > 0; zero-gap components are unrestricted; reason: this ensures finite aggregate threshold benchmark and hence finite optimal PA revenue by hbenchmark. On atomless source instances the threshold and optimal revenues agree almost surely; on finite supports the raised-threshold benchmark is finite. Infinite source benchmark revenues are excluded as DISPROOF.md requires. In the generalized domain hfin applies to B_j; zero-gap components remain unrestricted
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 24, Theorem 4 and its proof; Equations (9) p. 22 and (10) p. 23

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiUnit
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiProgram
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Mechanism
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Position
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_PositionSpp

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem_4 {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ℝ) (hα : IsCTR α) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (ht : ∀ j : Fin n, IsMultiThresholdMech ((j : ℕ) + 1) μ (t j))
    (M : Fin n → DirectMech n)
    (hopt : ∀ j : Fin n, IsOptimal μ (UnitFeasible ((j : ℕ) + 1)) (M j))
    (halloc : ∀ j v i, (M j).alloc v i = 0 ∨ (M j).alloc v i = 1)
    (hpay : ∀ j v i, 0 ≤ (M j).pay v i)
    (hbenchmark : ∀ j, ((M j).revenue μ).toENNReal ≤ optRev μ (t j))
    (hfin : ∀ j, 0 < ctrGap α j → optRev μ (t j) ≠ ⊤) :
    let Mopt := paMech α M
    let optPA : ℝ≥0∞ := (Mopt.revenue μ).toENNReal
    let f : Fin n → ℝ≥0∞ := fun j => ENNReal.ofReal (ctrGap α j) * ((M j).revenue μ).toENNReal / optPA
    IsOptimal μ (PAFeasibleClicks α) Mopt ∧
    ∑ j : Fin n, ENNReal.ofReal (ctrGap α j) * optRev μ (t j) * (frMulti ((j : ℕ) + 1))⁻¹ ≤
      paSppRev α μ t ∧
    (∃ p : Fin n → Fin n → ℝ, (∀ j i, 0 ≤ p j i) ∧
      (∀ j, (∃ τ : ℝ, p j = fun _ => τ) ∨ ∃ W : Fin n → Fin n → ℝ, p j = fun i => t j i (W i)) ∧
      (∀ v, PAFeasibleClicks α (paSppClicks α p v) ∧ ClickIneq α (paSppClicks α p v)) ∧
      IsTruthfulIR μ (PAFeasibleClicks α) (paSppMech α p) ∧
      ∑ j : Fin n, ENNReal.ofReal (ctrGap α j) * optRev μ (t j) * (frMulti ((j : ℕ) + 1))⁻¹ ≤
        paSppRevDet α μ p) ∧
    ENNReal.ofReal (6543 / 10000) ≤ (frMulti 1)⁻¹ ∧
    (0 < optPA →
      ∑ j, f j = 1 ∧
      (∑ j, f j * (frMulti ((j : ℕ) + 1))⁻¹) * optPA ≤ paSppRev α μ t ∧
      (frMulti 1)⁻¹ ≤ ∑ j, f j * (frMulti ((j : ℕ) + 1))⁻¹) := by sorry

end SPPRevenue.SingleUnit.Supplement
