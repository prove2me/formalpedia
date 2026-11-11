-- Prove2me | Theorems.Thm_ProdMomentConc_lemma_A_2_ii_eps_Lambda
-- name    : ProdMomentConc.lemma_A_2_ii_eps_Lambda
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:24.2192+00:00
-- url     : https://prove2.me/theorems/f1612ce9-403a-470e-8b16-95b74e4716d1
-- title:
--   Lemma A.2 (ii), eq. (12) — the induced read degree $\Lambda_k$ rarely exceeds $d_0$
-- statement:
--   Consider the bipartite dependency graph with read sets $P_1,\dots,P_n \subseteq [m]$, in which every underlying variable is read by at least one and at most $\Delta_L$ outputs. Let $d_0, k$ be positive integers with $k \le n$, let $I$ be a uniformly random $k$-subset of $[n]$, and let $\Lambda_k$ be the maximum left degree induced by $I$. Then
--
--   $$
--   \Pr_I[\Lambda_k > d_0] \le \exp\Big(-\Big[(d_0+1)\ln\frac{n}{k\Delta_L} + \ln\big((d_0+1)!\big) - \ln\frac{d_L m}{\Delta_L}\Big]\Big),
--   $$
--
--   that is, $\varepsilon_\Lambda := \Pr[\Lambda_k > d_0]$ satisfies (12): $\ln(1/\varepsilon_\Lambda) \ge (d_0+1)\ln\frac{n}{k\Delta_L} + \ln((d_0+1)!) - \ln\frac{d_L m}{\Delta_L}$. Equivalently, $\Pr[\Lambda_k > d_0] \le (k\Delta_L/n)^{d_0+1}\,(m d_L/\Delta_L)/(d_0+1)!$.
--
--   Combined with condition (8) of Theorem 3.5, this gives the first hypothesis of Lemma A.2 (i).
--
--   **Formalization Note** $\Lambda_k$ is `maxInducedDeg P I` with $I \sim$ `kSubsetLaw n k`, and $d_L$ is `dL P`. If $m \ge 1$, the hypotheses give $\Delta_L \ge 1$ and at least one edge, so every logarithm has a positive argument; if $m = 0$ the event is empty.
--
--   Differences from the source:
--   - encoding: ln(1/ε_Λ) ≥ c with Pr[Λ_k > d₀] ≤ ε_Λ → Pr_I[Λ_k > d₀] ≤ exp(−c); reason: equivalent, and defined when the probability is 0
--   - generalization: stated in the setting of Theorem 3.5 (r-wise independent bits, outputs with mean p, right degrees ≤ Δ_R, 1 ≤ r ≤ m, r ≥ Δ_R, d₀ ≤ Δ_L) → only the left-degree bound, the no-isolated-variable convention, 1 ≤ d₀ and 1 ≤ k ≤ n; reason: Λ_k and its law depend only on the graph; with the other hypotheses added it is the source's statement
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma A.2 (ii), eq. (12), p.34 (PDF p.34); proof p.35

import Mathlib
import Definitions.Def_ProdMomentConc_edgeCount
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_maxInducedDeg

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Lemma A.2 (ii), first estimate (12): the induced read degree.**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma A.2 (ii), eq. (12), p.34 (proof p.35).

For the bipartite dependency graph (left degrees at most `ΔL`, every left vertex of positive
degree), positive integers `d₀` and `k ≤ n`, and `I` a uniformly random `k`-subset of `[n]`,
`ε_Λ := Pr[Λ_k > d₀]` satisfies
`ln(1/ε_Λ) ≥ (d₀ + 1) ln(n/(kΔL)) + ln((d₀ + 1)!) − ln(d_L m/ΔL)`.

**Formalization Note.** Stated in the equivalent form
`Pr[Λ_k > d₀] ≤ exp(−((d₀ + 1) ln(n/(kΔL)) + ln((d₀ + 1)!) − ln(d_L m/ΔL)))` (which also covers
`Pr = 0`, where `ln(1/0)` is undefined). `Λ_k = maxInducedDeg P I`, `I ∼ kSubsetLaw n k`,
`d_L = dL P`. Under the hypotheses every logarithm has a positive argument when `m ≥ 1`
(`hused` gives `ΔL ≥ 1` and at least one edge). -/
theorem lemma_A_2_ii_eps_Lambda {m n : ℕ} (P : Fin n → Finset (Fin m)) (ΔL : ℕ)
    (hΔL : ∀ j, (Finset.univ.filter (fun i => j ∈ P i)).card ≤ ΔL)
    (hused : ∀ j, ∃ i, j ∈ P i) (d₀ k : ℕ) (hd₀ : 1 ≤ d₀) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (kSubsetLaw n k).real {S | d₀ < maxInducedDeg P S} ≤
      Real.exp (-(((d₀ : ℝ) + 1) * Real.log ((n : ℝ) / ((k : ℝ) * (ΔL : ℝ)))
        + Real.log ((d₀ + 1).factorial : ℝ) - Real.log (dL P * (m : ℝ) / (ΔL : ℝ)))) := by sorry

end ProdMomentConc
