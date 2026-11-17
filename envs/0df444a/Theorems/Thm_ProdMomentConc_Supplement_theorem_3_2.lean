-- Prove2me | Theorems.Thm_ProdMomentConc_Supplement_theorem_3_2
-- name    : ProdMomentConc.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:33:49.679487+00:00
-- url     : https://prove2.me/theorems/64064d29-599f-4bd2-8131-2852fedee6ad
-- title:
--   Theorem 3.2 — regular case under (5): $\Pr[\sum Y_i\ge\alpha n]\le 2e^{-(\lfloor r/d_R\rfloor/d_0)D(\alpha\|p)}$
-- statement:
--   Let $X_1,\dots,X_m\in\{0,1\}$ be $r$-wise independent random variables (every at most $r$ of them are mutually independent). For each output $i\in[n]$ let $P_i\subseteq[m]$ and $Y_i=f_i(X_{P_i})$ with $f_i:\{0,1\}^{P_i}\to[0,1]$, and suppose $\mathbb E[Y_i]=p$ for all $i$. The **dependency graph** is bipartite, with the bits as left vertices, the outputs as right vertices, and an edge $(j,i)$ iff $j\in P_i$. Underlying variables that appear in no output are discarded, and $1\le r\le m$. $D(\alpha\|p)=\alpha\ln\frac{\alpha}{p}+(1-\alpha)\ln\frac{1-\alpha}{1-p}$ is the binary relative entropy.
--
--   Assume, as in Theorem 3.1, that the dependency graph is $d_L$-$d_R$ regular (every bit read by exactly $d_L$ outputs, every output reading exactly $d_R$ bits) and $r\ge d_R$. Fix $0<p<\alpha<1$, and suppose that some integer $d_0$ with $1\le d_0\le d_L$ satisfies
--   $$d_0\ln\frac{m}{r}-\ln r+\ln\big((d_0+1)!\big)\ \ge\ \frac{r}{d_R}\Big(\frac{1}{d_0}-\frac{1}{d_L}\Big)\ln\frac{\alpha}{p}.\tag{5}$$
--   Then
--   $$\Pr\Big[\sum_{i=1}^n Y_i\ge\alpha n\Big]\le 2\exp\Big(-\frac{\lfloor r/d_R\rfloor}{d_0}\,D(\alpha\|p)\Big).$$
--
--   When $d_0<d_L$ this improves the leading exponent of Theorem 3.1 by the factor $d_L/d_0$: a uniformly random set of $\lfloor r/d_R\rfloor$ outputs typically induces a read degree much smaller than $d_L$.
--
--   **Formalization Note** In (5), $r/d_R$ is real division; in the conclusion $\lfloor r/d_R\rfloor$ is natural-number division. Condition (5) is required also when $d_0=d_L$, as on the page.
--
--   Differences from the source:
--   - encoding: X₁, …, Xₘ ∈ {0,1} r-wise independent random variables → Bool-valued measurable bits; r-wise independence is the published LaconicBarrier.KWiseIndep (iIndepFun on every set of at most r variables) of the bits read as reals in {0,1}; reason: a {0,1}-valued variable and its Bool version generate the same σ-algebra, so the instances are the same
--   - encoding: each Yᵢ a function of a subset of the Xⱼ, Yᵢ ∈ [0,1] → Yᵢ = f i (X restricted to P i) with P : Fin n → Finset (Fin m) and f i : (P i → Bool) → ℝ valued in [0,1]; E[Yᵢ] = p as a Bochner integral; reason: Definition 2.4's read-Δ model; every f i is bounded and takes finitely many values, so the integral is never junk
--   - encoding: read-d_L family whose dependency graph is a d_L-d_R regular bipartite graph, so that d_L m = d_R n → natural numbers dL, dR with every bit read by exactly dL outputs (hdL) and every output reading exactly dR bits (hdR); reason: regularity is exactly these degree equalities; read-d_L and d_L m = d_R n follow from them by double counting
--   - encoding: We discard underlying variables that appear in no output → hypothesis hused : ∀ j, ∃ i, j ∈ P i; reason: discarding unused variables is the same as assuming there are none
--   - encoding: ⌊r/d_R⌋ → natural-number division r / d_R, cast to ℝ; reason: the same value
--   - encoding: d₀ ∈ [d_L] → d₀ : ℕ with 1 ≤ d₀ ≤ dL; reason: [d_L] = {1, …, d_L}
--   - reading: In particular, whenever d₀ < d_L, this improves the leading exponent of Theorem 3.1 by a factor of d_L/d₀ → not stated; reason: a comparison of the exponent ⌊r/d_R⌋/d₀ with Theorem 3.1's ⌊r/d_R⌋/d_L, i.e. arithmetic on the two displayed bounds, not a further claim about the probability
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Theorem 3.2 with eq. (5), pp.12–13 (PDF pp.12–13; restated p.31, proof App. A.1, pp.31–33)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_LaconicBarrier_KWiseIndep

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc.Supplement

/-- **Theorem 3.2 (regular case, smaller induced read degree).** Saks, Srinivasan, Valieva,
*Concentration from Product Moments via an Additional Element of Randomness*, arXiv:2608.04125
(held version, sha256 5218e9d0…), Theorem 3.2, pp.12–13 (restated p.31; proof App. A.1, pp.31–33).

Under the assumptions of Theorem 3.1, fix `0 < p < α < 1`. If some `d₀ ∈ [d_L]` satisfies
`d₀ ln(m/r) − ln r + ln((d₀+1)!) ≥ (r/d_R)(1/d₀ − 1/d_L) ln(α/p)`   (5),
then `Pr[∑ Yᵢ ≥ αn] ≤ 2 exp(−(⌊r/d_R⌋/d₀) D(α‖p))`.

**Formalization Note.**
* The bits are `Bool`-valued; output `i` is `f i` applied to the restriction of the bit vector to
  `P i`, and `f i` takes values in `[0, 1]` (Definition 2.4, p.9).
* r-wise independence is the published `LaconicBarrier.KWiseIndep` (`iIndepFun` on every set of
  at most `r` variables) applied to the bits read as reals in `{0, 1}`, exactly as in the published
  `ProdMomentConc.theorem_3_5`.
* `D(α‖p)` is the published `LimitedPriceChanges.LowerBound.klBer α p`
  `= α ln(α/p) + (1 − α) ln((1 − α)/(1 − p))` (p.4).
* "We discard underlying variables that appear in no output" is the hypothesis `hused`.
* The regular dependency graph is encoded by exact degrees `dL`, `dR` (`hdL`, `hdR`), as in
  Theorem 3.1.
* `d₀ ∈ [d_L]` is `1 ≤ d₀ ≤ dL`. In (5), `r/d_R` is real division; in the conclusion `⌊r/d_R⌋`
  is natural-number division `r / dR`, cast to `ℝ`. Condition (5) is required also when
  `d₀ = d_L`, as on the page. The closing sentence of the theorem ("In particular … improves the
  leading exponent … by a factor of d_L/d₀") is commentary and has no Lean counterpart. -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m n : ℕ} (X : Fin m → Ω → Bool) (hXm : ∀ j, Measurable (X j))
    (r : ℕ)
    (hX : LaconicBarrier.KWiseIndep μ (fun j ω => if X j ω then (1 : ℝ) else 0) r)
    (P : Fin n → Finset (Fin m)) (f : (i : Fin n) → (P i → Bool) → ℝ)
    (hf : ∀ i b, 0 ≤ f i b ∧ f i b ≤ 1) (p : ℝ)
    (hmean : ∀ i, ∫ ω, f i (fun j => X j ω) ∂μ = p)
    (dL dR : ℕ) (hdL : ∀ j, (Finset.univ.filter (fun i => j ∈ P i)).card = dL)
    (hdR : ∀ i, (P i).card = dR) (hused : ∀ j, ∃ i, j ∈ P i)
    (hr1 : 1 ≤ r) (hrm : r ≤ m) (hrdR : dR ≤ r)
    (α : ℝ) (hp : 0 < p) (hpα : p < α) (hα1 : α < 1)
    (d₀ : ℕ) (hd₀ : 1 ≤ d₀) (hd₀dL : d₀ ≤ dL)
    (h5 : (r : ℝ) / (dR : ℝ) * (1 / (d₀ : ℝ) - 1 / (dL : ℝ)) * Real.log (α / p) ≤
      (d₀ : ℝ) * Real.log ((m : ℝ) / (r : ℝ)) - Real.log (r : ℝ)
        + Real.log ((d₀ + 1).factorial : ℝ)) :
    μ.real {ω | α * (n : ℝ) ≤ ∑ i, f i (fun j => X j ω)} ≤
      2 * Real.exp (-(((r / dR : ℕ) : ℝ) / (d₀ : ℝ)) *
        LimitedPriceChanges.LowerBound.klBer α p) := by sorry

end ProdMomentConc.Supplement
