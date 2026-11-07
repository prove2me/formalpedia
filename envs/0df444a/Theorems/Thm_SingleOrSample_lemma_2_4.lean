-- Prove2me | Theorems.Thm_SingleOrSample_lemma_2_4
-- name    : SingleOrSample.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:40.548178+00:00
-- url     : https://prove2.me/theorems/dd3154e8-150a-4bc3-9eab-7f67790a65ae
-- title:
--   Lemma 2.4 — exponential supermartingale with predictable charges
-- statement:
--   Let $(Y_r)_{r=0}^N$ be a real process adapted to a filtration $(\mathcal F_r)$ with $Y_0=0$, fix $\lambda\ge0$, and for $r=1,\dots,N$ let $b_r$ be a finite nonnegative $\mathcal F_{r-1}$-measurable random variable with
--   $$\mathbb E\bigl[e^{\lambda(Y_r-Y_{r-1})}\mid\mathcal F_{r-1}\bigr]\le e^{b_r}\quad\text{almost surely.}$$
--   Then:
--
--   1. for every $j\in\{0,\dots,N\}$, $\ \mathbb E\bigl[\exp\bigl(\lambda Y_j-\sum_{r=1}^jb_r\bigr)\bigr]\le1$;
--   2. the same holds for $j$ replaced by any stopping time $\tau\le N$;
--   3. if $\sum_{r=1}^\tau b_r\le B$ almost surely for a constant $B$, then $\mathbb E[e^{\lambda Y_\tau}]\le e^B$.
--
--   **Formalization Note** The conditional expectation is that of a $[0,\infty]$-valued function, Mathlib's `condLExp`, and the conclusions are Lebesgue integrals, since the exponentials need not be integrable. With the Bochner conditional expectation the hypothesis would hold vacuously on a non-integrable increment, and the lemma would be false. The underlying measure is a probability measure.
--
--   Differences from the source:
--   - encoding: a filtration (F_r) indexed by r ≤ N → a filtration indexed by ℕ, with only indices ≤ N in the statement; reason: a filtration on 0,…,N extends by constants
--   - encoding: E[·|F] and E[·] of possibly non-integrable exponentials → condLExp and ∫⁻ of the ℝ≥0∞-valued exponential; reason: these are the expectations of nonnegative functions; no integrability hypothesis is added
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 2.4, pp.8–9, restated p.33

import Mathlib

open MeasureTheory

namespace SingleOrSample

/-- **Lemma 2.4** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 2.4, pp.8–9, restated p.33). A process `Y` adapted to `(F_r)` with `Y_0 = 0`,
`λ ≥ 0`, and finite nonnegative `F_{r−1}`-measurable `b_r` with `E[e^{λ(Y_r − Y_{r−1})} | F_{r−1}] ≤ e^{b_r}`
almost surely satisfies `E[exp(λY_j − ∑_{r ≤ j} b_r)] ≤ 1` for every `j ≤ N`, the same at any stopping time
`τ ≤ N`, and `E[e^{λY_τ}] ≤ e^B` if `∑_{r ≤ τ} b_r ≤ B` almost surely.

**Formalization Note.** The conditional expectation is Mathlib's `condLExp` (`μ⁻[·|m]`) of the `ℝ≥0∞`-valued
exponential, and the conclusions are `∫⁻`, because the exponential need not be integrable. Bochner `condExp`
would be `0` on a non-integrable function, making hypothesis (1) vacuous and the lemma false. No integrability
hypothesis is added. The filtration is indexed by `ℕ`; only the indices up to `N` occur in the statement.
Mathlib's stopping times take values in `WithTop ℕ`, so the coercion of `τ` is used, with `τ ≤ N`. -/
theorem lemma_2_4 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (N : ℕ) (Y : ℕ → Ω → ℝ) (hY : ∀ r ≤ N, StronglyMeasurable[F r] (Y r))
    (hY0 : ∀ ω, Y 0 ω = 0) (lam : ℝ) (hlam : 0 ≤ lam) (b : ℕ → Ω → ℝ)
    (hb0 : ∀ r ∈ Finset.Icc 1 N, ∀ ω, 0 ≤ b r ω)
    (hbm : ∀ r ∈ Finset.Icc 1 N, Measurable[F (r - 1)] (b r))
    (hmgf : ∀ r ∈ Finset.Icc 1 N,
      μ⁻[fun ω => ENNReal.ofReal (Real.exp (lam * (Y r ω - Y (r - 1) ω)))|F (r - 1)] ≤ᵐ[μ]
        fun ω => ENNReal.ofReal (Real.exp (b r ω))) :
    (∀ j ≤ N, ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * Y j ω - ∑ r ∈ Finset.Icc 1 j, b r ω)) ∂μ ≤ 1) ∧
    ∀ τ : Ω → ℕ, IsStoppingTime F (fun ω => (τ ω : WithTop ℕ)) → (∀ ω, τ ω ≤ N) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * Y (τ ω) ω - ∑ r ∈ Finset.Icc 1 (τ ω), b r ω)) ∂μ ≤ 1 ∧
      ∀ B : ℝ, (∀ᵐ ω ∂μ, ∑ r ∈ Finset.Icc 1 (τ ω), b r ω ≤ B) →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * Y (τ ω) ω)) ∂μ ≤ ENNReal.ofReal (Real.exp B) := by sorry

end SingleOrSample
