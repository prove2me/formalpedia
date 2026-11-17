-- Prove2me | Theorems.Thm_ProdMomentConc_Supplement_theorem_3_4
-- name    : ProdMomentConc.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:34:18.062135+00:00
-- url     : https://prove2.me/theorems/56e52efb-1979-458d-ab6f-47cc415528bd
-- title:
--   Theorem 3.4 — general degrees: $\Pr[\sum Y_i\ge\alpha n]\le e^{-(\lfloor r/\Delta_R\rfloor/\Delta_L)D(\alpha\|p)}$
-- statement:
--   Let $X_1,\dots,X_m\in\{0,1\}$ be $r$-wise independent random variables (every at most $r$ of them are mutually independent). For each output $i\in[n]$ let $P_i\subseteq[m]$ and $Y_i=f_i(X_{P_i})$ with $f_i:\{0,1\}^{P_i}\to[0,1]$, and suppose $\mathbb E[Y_i]=p$ for all $i$. The **dependency graph** is bipartite, with the bits as left vertices, the outputs as right vertices, and an edge $(j,i)$ iff $j\in P_i$. Underlying variables that appear in no output are discarded, and $1\le r\le m$. $D(\alpha\|p)=\alpha\ln\frac{\alpha}{p}+(1-\alpha)\ln\frac{1-\alpha}{1-p}$ is the binary relative entropy.
--
--   Suppose the dependency graph has maximum left degree at most $\Delta_L$ (each bit is read by at most $\Delta_L$ outputs) and maximum right degree at most $\Delta_R$ (each output reads at most $\Delta_R$ bits), and assume $r\ge\Delta_R$. Then for every $0<p<\alpha<1$,
--   $$\Pr\Big[\sum_{i=1}^n Y_i\ge\alpha n\Big]\le\exp\Big(-\frac{\lfloor r/\Delta_R\rfloor}{\Delta_L}\,D(\alpha\|p)\Big).$$
--
--   This is the worst-case-degree baseline; the mission's goal (Theorem 3.5) improves the factor $\lfloor r/\Delta_R\rfloor/\Delta_L$ to $k/d_0$ at the cost of the constant $3$, so it does not imply this bound.
--
--   **Formalization Note** $\Delta_L,\Delta_R$ are degree bounds, not exact maxima. The setup is the same as in the published goal `ProdMomentConc.theorem_3_5`.
--
--   Differences from the source:
--   - encoding: X₁, …, Xₘ ∈ {0,1} r-wise independent random variables → Bool-valued measurable bits; r-wise independence is the published LaconicBarrier.KWiseIndep (iIndepFun on every set of at most r variables) of the bits read as reals in {0,1}; reason: a {0,1}-valued variable and its Bool version generate the same σ-algebra, so the instances are the same
--   - encoding: each Yᵢ a function of a subset of the Xⱼ, Yᵢ ∈ [0,1] → Yᵢ = f i (X restricted to P i) with P : Fin n → Finset (Fin m) and f i : (P i → Bool) → ℝ valued in [0,1]; E[Yᵢ] = p as a Bochner integral; reason: Definition 2.4's read-Δ model; every f i is bounded and takes finitely many values, so the integral is never junk
--   - encoding: We discard underlying variables that appear in no output → hypothesis hused : ∀ j, ∃ i, j ∈ P i; reason: discarding unused variables is the same as assuming there are none
--   - encoding: ⌊r/Δ_R⌋ → natural-number division r / Δ_R, cast to ℝ; reason: the same value
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Theorem 3.4, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_LaconicBarrier_KWiseIndep

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc.Supplement

/-- **Theorem 3.4 (general degrees, baseline).** Saks, Srinivasan, Valieva, *Concentration from
Product Moments via an Additional Element of Randomness*, arXiv:2608.04125 (held version, sha256
5218e9d0…), Theorem 3.4, p.15.

Let `X₁, …, Xₘ ∈ {0,1}` be `r`-wise independent and `Y₁, …, Yₙ ∈ [0,1]` with `E[Yᵢ] = p` for all
`i`, each `Yᵢ` a function of a subset of the `Xⱼ`, with dependency graph of maximum left degree at
most `Δ_L` and maximum right degree at most `Δ_R`. Discard underlying variables appearing in no
output and assume `1 ≤ r ≤ m` and `r ≥ Δ_R`. Then for every `0 < p < α < 1`,
`Pr[∑ Yᵢ ≥ αn] ≤ exp(−(⌊r/Δ_R⌋/Δ_L) D(α‖p))`.

**Formalization Note.**
* The bits are `Bool`-valued; output `i` is `f i` applied to the restriction of the bit vector to
  `P i`, and `f i` takes values in `[0, 1]` (Definition 2.4, p.9).
* r-wise independence is the published `LaconicBarrier.KWiseIndep` (`iIndepFun` on every set of
  at most `r` variables) applied to the bits read as reals in `{0, 1}`, exactly as in the published
  `ProdMomentConc.theorem_3_5`.
* `D(α‖p)` is the published `LimitedPriceChanges.LowerBound.klBer α p`
  `= α ln(α/p) + (1 − α) ln((1 − α)/(1 − p))` (p.4).
* "We discard underlying variables that appear in no output" is the hypothesis `hused`.
* `ΔL`, `ΔR` are degree bounds ("maximum left degree at most ∆L"), not the exact maxima.
* `⌊r/Δ_R⌋` is natural-number division `r / ΔR`, cast to `ℝ`. -/
theorem theorem_3_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m n : ℕ} (X : Fin m → Ω → Bool) (hXm : ∀ j, Measurable (X j))
    (r : ℕ)
    (hX : LaconicBarrier.KWiseIndep μ (fun j ω => if X j ω then (1 : ℝ) else 0) r)
    (P : Fin n → Finset (Fin m)) (f : (i : Fin n) → (P i → Bool) → ℝ)
    (hf : ∀ i b, 0 ≤ f i b ∧ f i b ≤ 1) (p : ℝ)
    (hmean : ∀ i, ∫ ω, f i (fun j => X j ω) ∂μ = p)
    (ΔL ΔR : ℕ) (hΔL : ∀ j, (Finset.univ.filter (fun i => j ∈ P i)).card ≤ ΔL)
    (hΔR : ∀ i, (P i).card ≤ ΔR) (hused : ∀ j, ∃ i, j ∈ P i)
    (hr1 : 1 ≤ r) (hrm : r ≤ m) (hrΔR : ΔR ≤ r)
    (α : ℝ) (hp : 0 < p) (hpα : p < α) (hα1 : α < 1) :
    μ.real {ω | α * (n : ℝ) ≤ ∑ i, f i (fun j => X j ω)} ≤
      Real.exp (-(((r / ΔR : ℕ) : ℝ) / (ΔL : ℝ)) *
        LimitedPriceChanges.LowerBound.klBer α p) := by sorry

end ProdMomentConc.Supplement
