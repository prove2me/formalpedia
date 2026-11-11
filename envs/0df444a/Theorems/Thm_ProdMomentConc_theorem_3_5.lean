-- Prove2me | Theorems.Thm_ProdMomentConc_theorem_3_5
-- name    : ProdMomentConc.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:18.346197+00:00
-- url     : https://prove2.me/theorems/03000884-aecc-42f0-b7f4-6d2d8357ac15
-- title:
--   Theorem 3.5 — read-$\Delta$ families over $r$-wise independent bits satisfy $\Pr[\sum Y_i \ge \alpha n] \le 3e^{-(k/d_0)D(\alpha\|p)}$
-- statement:
--   Let $X_1,\dots,X_m \in \{0,1\}$ be $r$-wise independent random variables, and let $Y_1,\dots,Y_n \in [0,1]$ satisfy $\mathbb E[Y_i] = p$ for all $i \in [n]$, where each $Y_i$ is a function of the variables $X_j$, $j \in P_i \subseteq [m]$. Suppose the dependency graph has maximum left degree at most $\Delta_L$ (each $X_j$ is read by at most $\Delta_L$ outputs) and maximum right degree at most $\Delta_R$ (each $Y_i$ reads at most $\Delta_R$ variables), that every underlying variable is read by some output, that $1 \le r \le m$, and that $r \ge \Delta_R$. Let $d_L$, $d_R$ be the average left and right degrees ($d_L m = d_R n$ = number of edges), and let $\chi$ be the fractional chromatic number of the graph on the underlying variables in which two variables are adjacent if they have a common output neighbour.
--
--   Fix $0 < p < \alpha < 1$ and positive integers $d_0, k$ with $d_0 \le \Delta_L$, $k \le n$ and $d_R k < r$. Suppose that, if $d_0 < \Delta_L$,
--
--   $$
--   (d_0+1)\ln\frac{n}{k\Delta_L} + \ln\big((d_0+1)!\big) - \ln\frac{d_L m}{\Delta_L} \ge k\Big(\frac{1}{d_0} - \frac{1}{\Delta_L}\Big)\ln\frac{\alpha}{p} \tag{8}
--   $$
--
--   (when $d_0 = \Delta_L$ this condition is omitted), and that
--
--   $$
--   (r - d_R k)^2 \max\Big\{\frac{1}{2k\Delta_R^2}, \frac{2}{m\chi}\Big\} \ge \Big(\frac{k}{d_0} - \frac{\lfloor r/\Delta_R\rfloor}{\Delta_L}\Big)\ln\frac{\alpha}{p}. \tag{9}
--   $$
--
--   Then
--
--   $$
--   \Pr\Big[\sum_{i=1}^n Y_i \ge \alpha n\Big] \le 3\exp\Big(-\frac{k}{d_0} D(\alpha\|p)\Big),
--   $$
--
--   where $D(\alpha\|p) = \alpha\ln\frac{\alpha}{p} + (1-\alpha)\ln\frac{1-\alpha}{1-p}$.
--
--   The direct argument limits the Chernoff exponent to $\lfloor r/\Delta_R\rfloor/\Delta_L$ times $D(\alpha\|p)$ (Theorem 3.4). The theorem replaces the worst-case read degree $\Delta_L$ by the read degree $d_0$ typically induced by a random set of $k$ outputs, and the worst-case $\lfloor r/\Delta_R\rfloor$ by a subset size $k$ limited only by the typical neighbourhood size $d_R k$.
--
--   **Formalization Note** The bits are `Bool`-valued, and $r$-wise independence is the published `LaconicBarrier.KWiseIndep` (every subfamily of at most $r$ variables mutually independent) applied to the bits read as reals in $\{0,1\}$. Output $i$ is a function $f_i$, with values in $[0,1]$, of the restriction of the bit vector to $P_i$. $\Delta_L, \Delta_R$ are degree bounds, not maxima. $d_L = E/m$ and $d_R = E/n$ with $E$ the number of edges. $\chi$ is `OAI.LinearListHadwiger.Fractional.number` of the auxiliary graph (an infimum over fractional covers by stable sets). $\lfloor r/\Delta_R\rfloor$ is natural-number division; (8) is an implication from $d_0 < \Delta_L$. The probability is `μ.real` of the event. $D(\alpha\|p)$ is the published binary relative entropy `LimitedPriceChanges.LowerBound.klBer α p`.
--
--   Differences from the source:
--   - encoding: X_j ∈ {0,1} r-wise independent, Yᵢ ∈ [0,1] a function of a subset of the X_j → Bool bits, KWiseIndep of their {0,1}-valued real versions, Yᵢ = fᵢ(X restricted to Pᵢ) with fᵢ ∈ [0,1]; reason: the same model (Bool and {0,1} ⊂ ℝ are in measurable bijection)
--   - encoding: "We discard underlying variables that appear in no output" → hypothesis that every j lies in some Pᵢ; reason: the source's standing convention, stated as a hypothesis
--   - encoding: "Suppose first that if d₀ < Δ_L, we have (8). When d₀ = Δ_L this condition is omitted" → hypothesis d₀ < Δ_L → (8); reason: the same condition
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Theorem 3.5, p.16 (PDF p.16), restated p.33; setup of Theorem 3.4, p.15; D(q‖p), p.4

import Mathlib
import Definitions.Def_OAIQWLLH000
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_ProdMomentConc_edgeCount
import Definitions.Def_ProdMomentConc_auxGraph

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Theorem 3.5 (read-Δ families over r-wise independent bits, general degrees).**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Theorem 3.5, p.16 (restated p.33).

Setup of Theorem 3.4 (p.15): bits `X₁, …, Xₘ ∈ {0,1}` that are `r`-wise independent; outputs
`Yᵢ = fᵢ(X_{Pᵢ}) ∈ [0, 1]` with `E[Yᵢ] = p` for all `i`; every underlying variable is read by at
most `ΔL` outputs and every output reads at most `ΔR` underlying variables; every underlying
variable is read by some output; `1 ≤ r ≤ m`, `r ≥ ΔR`. Let `χ` be the fractional chromatic number
of the auxiliary graph (`auxGraph P`), `0 < p < α < 1`, and `d₀, k` positive integers with
`d₀ ≤ ΔL`, `k ≤ n`, `d_R k < r`. If (8) holds when `d₀ < ΔL`, and (9) holds, then
`Pr[∑ Yᵢ ≥ αn] ≤ 3 exp(−(k/d₀) D(α‖p))`.

**Formalization Note.**
* The bits are `Bool`-valued; output `i` is `f i` applied to the restriction of the bit vector to
  `P i`, and `f i` takes values in `[0, 1]`.
* r-wise independence is the published `LaconicBarrier.KWiseIndep` (`iIndepFun` on every set of
  at most `r` variables) applied to the bits read as reals in `{0, 1}` (`true ↦ 1`, `false ↦ 0`);
  this is the same as mutual independence of every `r` of the `Bool`-valued bits.
* `D(α‖p)` is the published `LimitedPriceChanges.LowerBound.klBer α p`
  `= α ln(α/p) + (1 − α) ln((1 − α)/(1 − p))` (natural logarithm), as defined on p.4.
* `ΔL`, `ΔR` are degree bounds ("maximum left degree at most ΔL"), not the exact maxima.
* "We discard underlying variables that appear in no output" is the hypothesis `hused`.
* `d_L = E/m`, `d_R = E/n` with `E = ∑ᵢ |Pᵢ|` the number of edges (`dL`, `dR`).
* `χ` is `OAI.LinearListHadwiger.Fractional.number`: the infimum of the total weight of fractional
  covers of the vertices by stable sets.
* `⌊r/ΔR⌋` is natural-number division `r / ΔR`, cast to `ℝ`; (8) is an implication from `d₀ < ΔL`
  ("When d0 = ∆L this condition is omitted"). -/
theorem theorem_3_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m n : ℕ} (X : Fin m → Ω → Bool) (hXm : ∀ j, Measurable (X j))
    (r : ℕ)
    (hX : LaconicBarrier.KWiseIndep μ (fun j ω => if X j ω then (1 : ℝ) else 0) r)
    (P : Fin n → Finset (Fin m)) (f : (i : Fin n) → (P i → Bool) → ℝ)
    (hf : ∀ i b, 0 ≤ f i b ∧ f i b ≤ 1) (p : ℝ)
    (hmean : ∀ i, ∫ ω, f i (fun j => X j ω) ∂μ = p)
    (ΔL ΔR : ℕ) (hΔL : ∀ j, (Finset.univ.filter (fun i => j ∈ P i)).card ≤ ΔL)
    (hΔR : ∀ i, (P i).card ≤ ΔR) (hused : ∀ j, ∃ i, j ∈ P i)
    (hr1 : 1 ≤ r) (hrm : r ≤ m) (hrΔR : ΔR ≤ r)
    (α : ℝ) (hp : 0 < p) (hpα : p < α) (hα1 : α < 1)
    (d₀ k : ℕ) (hd₀ : 1 ≤ d₀) (hk : 1 ≤ k) (hd₀ΔL : d₀ ≤ ΔL) (hkn : k ≤ n)
    (hdRk : dR P * (k : ℝ) < (r : ℝ))
    (h8 : d₀ < ΔL →
      (k : ℝ) * (1 / (d₀ : ℝ) - 1 / (ΔL : ℝ)) * Real.log (α / p) ≤
        ((d₀ : ℝ) + 1) * Real.log ((n : ℝ) / ((k : ℝ) * (ΔL : ℝ)))
          + Real.log ((d₀ + 1).factorial : ℝ) - Real.log (dL P * (m : ℝ) / (ΔL : ℝ)))
    (h9 : ((k : ℝ) / (d₀ : ℝ) - ((r / ΔR : ℕ) : ℝ) / (ΔL : ℝ)) * Real.log (α / p) ≤
      ((r : ℝ) - dR P * (k : ℝ)) ^ 2 *
        max (1 / (2 * (k : ℝ) * (ΔR : ℝ) ^ 2))
          (2 / ((m : ℝ) * OAI.LinearListHadwiger.Fractional.number (auxGraph P)))) :
    μ.real {ω | α * (n : ℝ) ≤ ∑ i, f i (fun j => X j ω)} ≤
      3 * Real.exp (-((k : ℝ) / (d₀ : ℝ)) * LimitedPriceChanges.LowerBound.klBer α p) := by sorry

end ProdMomentConc
