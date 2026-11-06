-- Prove2me | Theorems.Thm_PADMPriv_lemma_A7
-- name    : PADMPriv.lemma_A7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:33.469208+00:00
-- url     : https://prove2.me/theorems/3cdc2b30-55bf-4bee-95e7-aea1bd369aa2
-- title:
--   Lemma A7 — a random-index mixture has Rényi divergence at most $\frac{e^h-1}{h}\,\mathbb E_{k\sim\rho}D_\alpha(\tilde u_{(k)}\|\tilde u'_{(k)})$
-- statement:
--   Let $\alpha>1$ and $h>0$, and let $\tilde u_{(k)}$, $\tilde u'_{(k)}$ ($k\in[n]$) be random variables with laws $\mu_k$, $\mu'_k$ such that $D_\alpha(\mu_k\|\mu'_k)\le\frac{h}{\alpha-1}$ for all $k$. Let $K$ be drawn from $[n]$ with distribution $\rho$, independently, the same for both sequences. Then
--   $$
--   D_\alpha\big(\tilde u_{(K)}\,\big\|\,\tilde u'_{(K)}\big)\le\frac{e^h-1}{h}\,\mathbb E_{k\sim\rho}\big[D_\alpha(\tilde u_{(k)}\|\tilde u'_{(k)})\big]. \tag{50}
--   $$
--
--   The lemma converts the per-step guarantees of Theorem 4.1 into a guarantee for a randomly stopped output (Theorem 4.2).
--
--   **Formalization Note** The law of $\tilde u_{(K)}$ is the mixture $\sum_k\rho_k\mu_k$, so the statement is about probability measures $\mu_k$, $\mu'_k$ on a measurable space and weights $\rho_k\ge0$ summing to $1$.
--
--   Differences from the source:
--   - encoding: random variables ũ₍ₖ₎, ũ′₍ₖ₎ and an independent index K ∼ ρ → probability measures μ_k, μ′_k and the mixtures ∑ ρ_k μ_k, ∑ ρ_k μ′_k; reason: the law of ũ₍K₎ is exactly that mixture
--   - encoding: the Rényi divergence of Definition 2 → computed through dP/dQ, +∞ when P is not absolutely continuous with respect to Q; reason: equal to Definition 2 for α > 1
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Lemma A7, p.24 (proof pp.24–25)

import Mathlib
import Definitions.Def_PADMPriv_renyiDiv

namespace PADMPriv

open MeasureTheory

/-- Lemma A7 of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.24 (proof pp.24–25): for `α > 1`, if
`D_α(ũ₍ₖ₎‖ũ′₍ₖ₎) ≤ h/(α − 1)` for all `k ∈ [n]` and some `h > 0`, and `K` is sampled independently
from `[n]` with the same distribution `ρ` for both sequences, then
`D_α(ũ₍K₎‖ũ′₍K₎) ≤ ((e^h − 1)/h) E_{k∼ρ}[D_α(ũ₍ₖ₎‖ũ′₍ₖ₎)]` (50).

**Formalization Note** The law of `ũ₍K₎` with `K ∼ ρ` independent is the mixture `∑ₖ ρₖ μₖ` of the
laws `μₖ` of `ũ₍ₖ₎`, so the lemma is stated for probability measures `μₖ`, `μ′ₖ` on a measurable
space and weights `ρ : Fin n → ℝ≥0` summing to one; `[n]` is `Fin n`. -/
theorem lemma_A7 {X : Type*} [MeasurableSpace X] {n : ℕ} (α : ℝ) (hα : 1 < α)
    (μ μ' : Fin n → Measure X) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, IsProbabilityMeasure (μ' k)] (h : ℝ) (hh : 0 < h)
    (hbound : ∀ k, renyiDiv α (μ k) (μ' k) ≤ ((h / (α - 1) : ℝ) : EReal))
    (ρ : Fin n → NNReal) (hρ : ∑ k, ρ k = 1) :
    renyiDiv α (∑ k, ρ k • μ k) (∑ k, ρ k • μ' k) ≤
      (((Real.exp h - 1) / h : ℝ) : EReal) *
        ∑ k, (((ρ k : ℝ)) : EReal) * renyiDiv α (μ k) (μ' k) := by sorry

end PADMPriv
