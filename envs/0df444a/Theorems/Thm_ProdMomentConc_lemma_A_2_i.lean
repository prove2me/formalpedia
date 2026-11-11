-- Prove2me | Theorems.Thm_ProdMomentConc_lemma_A_2_i
-- name    : ProdMomentConc.lemma_A_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:26.521473+00:00
-- url     : https://prove2.me/theorems/f38d325e-cf71-47b5-a316-616c2b4f01a0
-- title:
--   Lemma A.2 (i) — the two bad-event conditions suffice for (7)
-- statement:
--   Assume the setup of Theorem 3.4: $X_1,\dots,X_m \in \{0,1\}$ are $r$-wise independent; $Y_1,\dots,Y_n \in [0,1]$ satisfy $\mathbb E[Y_i] = p$ for all $i$, each $Y_i$ is a function of the variables indexed by $P_i \subseteq [m]$; every underlying variable is read by at most $\Delta_L$ outputs and by at least one, every output reads at most $\Delta_R$ underlying variables; $1 \le r \le m$ and $r \ge \Delta_R$. Let $0 < p < \alpha < 1$ and let $d_0, k$ be positive integers with $d_0 \le \Delta_L$ and $k \le n$. Let $I$ be a uniformly random $k$-subset of $[n]$, and let $L_k$, $\Lambda_k$ be the number of underlying variables read by $I$ and the maximum left degree induced by $I$. If
--
--   $$
--   \Pr_I[\Lambda_k > d_0] \le \exp\Big(-k\Big(\frac{1}{d_0} - \frac{1}{\Delta_L}\Big)\ln\frac{\alpha}{p}\Big)
--   \quad\text{and}\quad
--   \Pr_I[L_k > r] \le \exp\Big(-\Big[\Big(\frac{k}{d_0} - \frac{\lfloor r/\Delta_R\rfloor}{\Delta_L}\Big)\ln\frac{\alpha}{p}\Big]_+\Big),
--   $$
--
--   then (7) holds:
--
--   $$
--   \Pr\Big[\sum_{i=1}^n Y_i \ge \alpha n\Big] \le 3\exp\Big(-\frac{k}{d_0} D(\alpha\|p)\Big).
--   $$
--
--   The paper states the two conditions as $\ln(1/\varepsilon_\Lambda) \ge k(1/d_0 - 1/\Delta_L)\ln(\alpha/p)$ and $\ln(1/\varepsilon_L) \ge [\,\cdot\,]_+$ for bounds $\Pr[\Lambda_k > d_0] \le \varepsilon_\Lambda$, $\Pr[L_k > r] \le \varepsilon_L$. The lemma isolates the probabilistic core of the main theorem: once the two bad events of the random induced subgraph are rare enough, each contributes at most the good term $G = \exp(-(k/d_0)D(\alpha\|p))$.
--
--   **Formalization Note** The bits are `Bool`-valued; $r$-wise independence is the published `LaconicBarrier.KWiseIndep` applied to the bits read as reals in $\{0,1\}$. Output $i$ is a $[0,1]$-valued function of the restriction of the bit vector to $P_i$. $\Delta_L, \Delta_R$ are degree bounds. $\Pr_I$ is `kSubsetLaw n k`, $L_k$ is `Lk P I`, $\Lambda_k$ is `maxInducedDeg P I`, $\lfloor r/\Delta_R\rfloor$ is natural-number division and $[x]_+ = \max(0, x)$.
--
--   Differences from the source:
--   - encoding: ln(1/ε_Λ) ≥ c and ln(1/ε_L) ≥ c′ for some bounds Pr[Λ_k > d₀] ≤ ε_Λ, Pr[L_k > r] ≤ ε_L → Pr_I[Λ_k > d₀] ≤ exp(−c) and Pr_I[L_k > r] ≤ exp(−c′); reason: the two forms are equivalent (take ε = exp(−c)), and the exp form is also defined when the probability is 0
--   - encoding: X_j ∈ {0,1} r-wise independent, Yᵢ ∈ [0,1] a function of a subset of the X_j → Bool bits, KWiseIndep of their {0,1}-valued real versions, Yᵢ = fᵢ(X restricted to Pᵢ) with fᵢ ∈ [0,1]; reason: the same model
--   - encoding: "We discard underlying variables that appear in no output" → hypothesis that every j lies in some Pᵢ; reason: the source's standing convention, stated as a hypothesis
--   - generalization: stated inside the proof of Theorem 3.5, whose hypotheses also include d_R k < r, (8) and (9) → none of d_R k < r, (8), (9) assumed; reason: part (i) uses only the two displayed conditions (part (ii) states "if r > d_R k" separately); with those hypotheses added it is the source's statement
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma A.2 (i), p.34 (PDF p.34); ε_L, ε_Λ and (7) on p.16; setup of Theorem 3.4, p.15

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_ProdMomentConc_kSubsetLaw
import Definitions.Def_ProdMomentConc_Lk
import Definitions.Def_ProdMomentConc_maxInducedDeg

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Lemma A.2 (i): reduction of (7) to the two bad events.**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma A.2 (i), p.34 (with the definitions of `ε_L, ε_Λ` on p.16 and of (7) on p.16).

Under the setup of Theorem 3.4 (p.15), with positive integers `d₀ ≤ ΔL` and `k ≤ n`, let `I` be a
uniformly random `k`-subset of `[n]`, `Pr[L_k > r] ≤ ε_L` and `Pr[Λ_k > d₀] ≤ ε_Λ`. If
`ln(1/ε_Λ) ≥ k(1/d₀ − 1/ΔL) ln(α/p)` and `ln(1/ε_L) ≥ [(k/d₀ − ⌊r/ΔR⌋/ΔL) ln(α/p)]₊`, then (7):
`Pr[∑ Yᵢ ≥ αn] ≤ 3 exp(−(k/d₀) D(α‖p))`.

**Formalization Note.** "There is `ε > 0` with `Pr[A] ≤ ε` and `ln(1/ε) ≥ c`" is equivalent to
`Pr[A] ≤ exp(−c)`; the two hypotheses are stated in that form (`hΛ`, `hL`), with
`[x]₊ = max 0 x`. `Pr_I` is `kSubsetLaw n k`, `L_k = Lk P I`, `Λ_k = maxInducedDeg P I`. The model
of Theorem 3.4 is encoded as in `theorem_3_5` (`Bool` bits, r-wise independence as the published `LaconicBarrier.KWiseIndep`
of the `{0,1}`-valued real versions of the bits, outputs `f i` of the
bits in `P i` with values in `[0, 1]` and mean `p`, degree bounds `ΔL`, `ΔR`, `hused`); `⌊r/ΔR⌋`
is natural-number division; `D(α‖p)` is the published `LimitedPriceChanges.LowerBound.klBer α p`. -/
theorem lemma_A_2_i {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
    (hΛ : (kSubsetLaw n k).real {S | d₀ < maxInducedDeg P S} ≤
      Real.exp (-((k : ℝ) * (1 / (d₀ : ℝ) - 1 / (ΔL : ℝ)) * Real.log (α / p))))
    (hL : (kSubsetLaw n k).real {S | r < Lk P S} ≤
      Real.exp (-(max 0 (((k : ℝ) / (d₀ : ℝ) - ((r / ΔR : ℕ) : ℝ) / (ΔL : ℝ)) *
        Real.log (α / p))))) :
    μ.real {ω | α * (n : ℝ) ≤ ∑ i, f i (fun j => X j ω)} ≤
      3 * Real.exp (-((k : ℝ) / (d₀ : ℝ)) * LimitedPriceChanges.LowerBound.klBer α p) := by sorry

end ProdMomentConc
