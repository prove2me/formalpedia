-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_gamma_sum_L_tendsto_zero
-- name    : PooledRationing.MaxWeighted.gamma_sum_L_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:35.632235+00:00
-- url     : https://prove2.me/theorems/47260cfa-0a94-43f2-a4cf-6c94d6e3c268
-- title:
--   Proof of Theorem 3, p. 53 — lim_T γ_T Σ_{t≤T} L_t = 0 almost surely
-- statement:
--   Work under Assumptions 1 and 3 with $R_j\ge0$ and $s\le D$ on $P(c,D)$ for $D\ge0$, and let $w\mapsto\varphi_w$ be a selection of optimal solutions of (16) that is jointly measurable in $(w,D)$. Let $D^{(1)},D^{(2)},\dots$ be independent random demand vectors on a probability space, each with law $F$. For a horizon $T$ run Algorithm 1 on $D^{(1)},\dots,D^{(T)}$ with step $\gamma_T=T^{-(1/2+\epsilon)}$, $\epsilon\in(0,1/2)$, and let $L_t$ ($t=1,\dots,T$) be the terms (55) of this run. Then
--   $$\lim_{T\to\infty}\gamma_T\sum_{t=1}^TL_t=0\qquad\text{almost surely.}$$
--
--   The $L_t$ are bounded martingale differences for each fixed $T$, but they depend on $T$ through $\gamma_T$ and the iterates, so this is a law of large numbers for a triangular array. It removes the noise term from (57) and from the bound on the iterates in Lemma 6.
--
--   **Formalization Note.** All horizons $T$ read the first $T$ entries of one i.i.d. sequence; the paper draws the samples for each $T$ without coupling them, and its almost-sure statement needs a single probability space. Indices are 0-based (the Lean sum over $t=0,\dots,T-1$ is the page's sum over $t=1,\dots,T$). Measurability of $R_j$ and of the selection $(w,D)\mapsto\varphi_w(D)$ is assumed so that the iterates are random variables; these are not on the page. The feasibility of $c$ is not needed for this step.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 53, proof of Theorem 3, display after 'Thus, it holds that' (via Lemmas 4–5)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm

namespace PooledRationing.MaxWeighted

open MeasureTheory ProbabilityTheory Filter Topology

theorem gamma_sum_L_tendsto_zero
    {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRmono : ∀ j d, Monotone (fun s => R j s d))
    (hRusc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hPcpt : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (B : ℝ) (hA3supp : ∀ᵐ D ∂F, ∀ j, |D j| ≤ B)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → (Fin n → ℝ)) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (ϵ : ℝ) (hϵ : ϵ ∈ Set.Ioo 0 (1 / 2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => stepSize ϵ T *
        ∑ t ∈ Finset.range T, Lterm F R β sel (stepSize ϵ T) T (fun k => Dseq k ω) t)
      atTop (𝓝 0) := by sorry

end PooledRationing.MaxWeighted
