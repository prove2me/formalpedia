-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_theorem_5
-- name    : SPPRevenue.SingleUnit.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:20:44.256079+00:00
-- url     : https://prove2.me/theorems/05c71487-febb-4fdb-8d5f-4a1420489b36
-- title:
--   Theorem 5 (corrected: s ∈ [0,1], finite revenue, 0.6620 as a rounding) — ESP auctions earn Opt/FR-ESP and Opt/FR-ESP-d(k)
-- statement:
--   Let $\mathrm{FR\text{-}ESP}$ be the optimal value of
--   $$\max_s\int_0^\infty s(\tau)\,d\tau\ \ \text{s.t.}\ \ \int_{T_x}^\infty\big(2-2e^{-s(\tau)}-s(\tau)e^{-s(\tau)}\big)d\tau+\int_0^{T_x}\big(x+1-e^{-s(\tau)}\big)d\tau\le2\ \ (x\in[0,1]),\ \ \int_0^\infty\big(1-e^{-s(\tau)}\big)d\tau\le1,$$
--   over weakly decreasing $s:[0,\infty)\to[0,1]$, where $T_x=\inf\{\tau\ge0:s(\tau)\le x\}$ ($\infty$ if there is none). For an integer $k\ge1$ and $s_i=i/k$, let $\mathrm{FR\text{-}ESP\text{-}d}(k)$ be the optimal value of
--   $$\max_{w\ge0}\sum_{i\in[k]}w_i\ \ \text{s.t.}\ \ \sum_{i=1}^jw_i\frac{2(1-e^{-s_i})-s_ie^{-s_i}}{s_i}+\sum_{i=j+1}^kw_i\frac{s_j+1-e^{-s_i}}{s_i}\le2\ (j\in[k]),\ \ \sum_{i\in[k]}w_i\frac{1-e^{-s_i}}{s_i}\le1.$$
--   Then:
--
--   1. both programs attain their maximum, which is positive and finite, for every $k\ge1$;
--   2. $1/\mathrm{FR\text{-}ESP\text{-}d}(3200)$ rounds to $0.6620$ at four decimals;
--   3. for every single-unit setting with $n\ge1$ buyers, independent values and a threshold mechanism (for instance the optimal one) of finite expected revenue $\mathrm{Opt}$, there are nonnegative reserve prices $p$ with
--   $$\mathrm{ESP}(p)\ \ge\ \mathrm{Opt}\cdot\frac1{\mathrm{FR\text{-}ESP}}\qquad\text{and}\qquad \mathrm{ESP}(p)\ \ge\ \mathrm{Opt}\cdot\frac1{\mathrm{FR\text{-}ESP\text{-}d}(k)}\ \text{ for every integer }k\ge1.$$
--
--   The eager second-price auction exploits the second-highest bid and so beats the 0.6543 of posted prices.
--
--   **Formalization Note** $\mathrm{ESP}(p)$ is the expected revenue of the eager second-price auction with reserves $p$ (§7). The exact value of $1/\mathrm{FR\text{-}ESP\text{-}d}(3200)$ is about $0.661988$, so the printed "$=0.6620$" is a four-decimal rounding and is stated as one.
--
--   Differences from the source:
--   - generalization: Opt is the revenue of the optimal mechanism, for atomless or finitely supported laws → optRev of any single-unit threshold mechanism, for arbitrary value laws; reason: the proof uses only the feasible threshold benchmark. For atomless source laws, the optimal allocation and payments agree with the weak-threshold formula almost surely. For finite discrete laws, footnote 5 raises only losing-tie thresholds: allocations on the support stay the same and payments weakly increase. Thus the constructed benchmark dominates the source optimal revenue; exact payment preservation is not asserted. This does not say that every arbitrary threshold benchmark dominates Opt
--   - correction: no assumption on the optimal revenue → optRev μ t ≠ ⊤; reason: the independent atomless laws P[v₁≥x]=x^(−1/2) and P[v₂≥x]=x^(−1) for x≥1 admit the feasible truthful thresholds t₁=max(1,v₂)², t₂=√max(0,v₁)+1 with infinite revenue. Every fixed SPP or ESP has finite revenue (for ESP, E[min(v₁,v₂)]=3). DISPROOF.md checks the assumptions and calculations; the source normalization to unit revenue does not apply to this instance
--   - reading: the displayed program leaves the range of the candidate tail implicit → s(τ) ∈ [0, 1] for τ ≥ 0; reason: p. 27 defines f only for arguments in [0,1]; s⋆ is a probability tail and the grid is in (0,1]. The n-dependent program uses the same tail range under the substitution on p. 29. An unrestricted s>1 is outside this source-supported reading
--   - correction: T_x = inf{τ : s⋆(τ) ≤ x} inside the program → T_x = inf{τ ≥ 0 : s(τ) ≤ x} of the program's variable s, with inf ∅ = ∞; reason: the program optimizes over s; the proof (pp. 42–43) evaluates T_x on the feasible tail s⋆, which is the same thing at s = s⋆
--   - reading: FR-ESP and FR-ESP-d(k) is defined as a max → the program's value is the supremum of its objective values and the statement asserts that it is attained, positive and finite (IsFactorProgram); reason: the source writes max; the formal statement proves that the max exists rather than assuming it
--   - correction: 1/FR-ESP-d(3200) = 0.6620 → RoundsTo4 (1/FR-ESP-d(3200)) 6620, i.e. 0.66195 ≤ 1/FR-ESP-d(3200) < 0.66205; reason: the source reports four decimals; the brief records the diagnostic LP ratio ≈0.66198755, consistent with this rounding interval. Floating-point primal/dual agreement is not a rigorous certificate; the Lean conclusion is the certification task
--   - generalization: there exists a vector of prices p → there exist prices p with p i ≥ 0 for all i; reason: a stronger conclusion: the prices found are nonnegative
--   - encoding: an n-buyer setting, [n] = {1, …, n} → 1 ≤ n, buyers Fin n (index i is buyer i + 1); reason: n ≥ 1 is the setting's standing range; q_n and r_n are undefined at n = 0
--   - encoding: ESP(p) with argmax and second-highest surviving bid → winner: highest surviving value, ties to the lowest index; payment max(p_winner, highest other surviving value), p_winner if alone, 0 if nobody survives; reason: ties do not change the payment; same revenue
--   - encoding: ∫_{T_x}^∞ and ∫_0^{T_x} → integrals over {τ ≥ 0 : T_x ≤ τ} and {τ ≥ 0 : τ < T_x}; reason: differ only at the point T_x
--   - encoding: revenues and probabilities as real expectations → values in [0, ∞] (lower integrals and measures); the factor 1/FR as an inverse in [0, ∞]; reason: Lean convention; a revenue cannot collapse to a junk value and no instance changes
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 27, Theorem 5, (FR-ESP), (FR-ESP-d); Table 5 p. 28; proof §8.7, pp. 41–43

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_EspProgram
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Esp

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem_5 :
    IsFactorProgram (espValues qLim rLim) ∧
    (∀ k : ℕ, 1 ≤ k → IsFactorProgram (espDValues qLim rLim k)) ∧
    RoundsTo4 (frEspD 3200)⁻¹.toReal 6620 ∧
    ∀ n : ℕ, 1 ≤ n → ∀ (μ : Fin n → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
      ∀ (t : Fin n → (Fin n → ℝ) → ℝ), IsThresholdMech μ t → optRev μ t ≠ ⊤ →
        ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧
          frEsp⁻¹ * optRev μ t ≤ espRev μ p ∧
          ∀ k : ℕ, 1 ≤ k → (frEspD k)⁻¹ * optRev μ t ≤ espRev μ p := by sorry

end SPPRevenue.SingleUnit.Supplement
