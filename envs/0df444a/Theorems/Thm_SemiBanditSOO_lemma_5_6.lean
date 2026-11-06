-- Prove2me | Theorems.Thm_SemiBanditSOO_lemma_5_6
-- name    : SemiBanditSOO.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:00.163684+00:00
-- url     : https://prove2.me/theorems/4c0664de-281d-4660-8e14-fedebcc7a51b
-- title:
--   Lemma 5.6 — $\mathbb E[\sum_h\mathrm{Var}(Y_{h+1}\mid\mathcal F_h)]\le\mathbb E[Y_H^2]-\mathbb E[Y_0^2]+2\mathbb E[\sum_h(d_h)_+]$, and $\le1$ for a supermartingale
-- statement:
--   Let $(Y_h)_{h=0}^H$ be a process adapted to a filtration $(\mathcal F_h)_{h=0}^H$ and taking values in $[0,1]$, and let $d_h=Y_h-\mathbb E[Y_{h+1}\mid\mathcal F_h]$ for $0\le h<H$. Then
--   $$\mathbb E\Bigl[\sum_{h=0}^{H-1}\mathrm{Var}(Y_{h+1}\mid\mathcal F_h)\Bigr]\le\mathbb E[Y_H^2]-\mathbb E[Y_0^2]+2\,\mathbb E\Bigl[\sum_{h=0}^{H-1}(d_h)_+\Bigr].$$
--   If, in addition, $(Y_h)$ is a supermartingale, that is, $d_h\ge0$ for every $h$, then the right-hand side is at most $1$.
--
--   Applied to the optimistic values along the path of one round, this bounds the total conditional variance of a round by $1$.
--
--   **Formalization Note.** The filtration is indexed by $\mathbb N$ and only $\mathcal F_0,\dots,\mathcal F_H$ enter; conditional variance is Mathlib's `condVar`. Conditional expectations are defined almost everywhere, so $d_h\ge0$ is required almost everywhere.
--
--   Differences from the source:
--   - encoding: a filtration (𝓕_h)_{h=0}^H → a filtration indexed by ℕ, of which 𝓕_0, …, 𝓕_H enter; reason: every finite filtration extends to ℕ (constant after H); the statement involves only h ≤ H
--   - encoding: d_h ≥ 0 for every h → 0 ≤ d_h almost everywhere, for h < H; reason: conditional expectations are defined almost everywhere
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Lemma 5.6, p.23

import Mathlib

open MeasureTheory

namespace SemiBanditSOO

/-- **Lemma 5.6 (variance budget of a `[0, 1]`-valued process).** Harada, Kawase, Sumita, *Beyond
Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1,
Lemma 5.6, p.23.

Let `(Y_h)_{h=0}^H` be a process adapted to a filtration `(ℱ_h)_{h=0}^H` and taking values in
`[0, 1]`, and let `d_h = Y_h − 𝔼[Y_{h+1} | ℱ_h]` for `0 ≤ h < H`. Then
`𝔼[Σ_{h=0}^{H−1} Var(Y_{h+1} | ℱ_h)] ≤ 𝔼[Y_H²] − 𝔼[Y_0²] + 2 𝔼[Σ_{h=0}^{H−1} (d_h)₊]`.
If, in addition, `(Y_h)` is a supermartingale, that is, `d_h ≥ 0` for every `h`, then the
right-hand side is at most `1`.

**Formalization Note.** The filtration is indexed by `ℕ` (only `ℱ_0, …, ℱ_H` enter); the process is
constrained only for `h ≤ H`. `Var(· | ℱ_h)` is Mathlib's `condVar`. Conditional expectations are
defined almost everywhere, so "`d_h ≥ 0`" is `0 ≤ d_h` almost everywhere. -/
theorem lemma_5_6 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (H : ℕ)
    (hadapt : ∀ h ≤ H, StronglyMeasurable[ℱ h] (Y h))
    (hY01 : ∀ h ≤ H, ∀ ω, Y h ω ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, ∑ h ∈ Finset.range H, ProbabilityTheory.condVar (ℱ h) (Y (h + 1)) μ ω ∂μ ≤
      ∫ ω, Y H ω ^ 2 ∂μ - ∫ ω, Y 0 ω ^ 2 ∂μ +
        2 * ∫ ω, ∑ h ∈ Finset.range H, max (Y h ω - (μ[Y (h + 1) | ℱ h]) ω) 0 ∂μ) ∧
    ((∀ h < H, 0 ≤ᵐ[μ] fun ω => Y h ω - (μ[Y (h + 1) | ℱ h]) ω) →
      ∫ ω, Y H ω ^ 2 ∂μ - ∫ ω, Y 0 ω ^ 2 ∂μ +
        2 * ∫ ω, ∑ h ∈ Finset.range H, max (Y h ω - (μ[Y (h + 1) | ℱ h]) ω) 0 ∂μ ≤ 1) := by sorry

end SemiBanditSOO
