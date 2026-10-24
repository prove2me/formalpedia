-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_lemma_6
-- name    : PooledRationing.MaxWeighted.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:28.617059+00:00
-- url     : https://prove2.me/theorems/4e3849d7-633f-414e-94b5-bb9df27479ef
-- title:
--   Lemma 6, p. 54 — if c is feasible, w_j^(T+1)/(Tγ_T) → 0 almost surely
-- statement:
--   Work in the setting of Theorem 3: Assumptions 1 and 3, $c$ feasible, $|f|\le K$ on feasible allocations, $R_j\ge0$, $s\le D$ on $P(c,D)$ for $D\ge0$, a selection $w\mapsto\varphi_w$ of optimal solutions of (16) that is jointly measurable in $(w,D)$, independent demand samples $D^{(1)},D^{(2)},\dots$ with law $F$, and the step size $\gamma_T=T^{-(1/2+\epsilon)}$ with $\epsilon\in(0,1/2)$. Let $w^{(T+1)}$ be the last iterate (26) of Algorithm 1 run on $D^{(1)},\dots,D^{(T)}$ with step $\gamma_T$. Then for every customer $j\in N$,
--   $$\limsup_{T\to\infty}\frac{w^{(T+1)}_j}{T\gamma_T}=0\qquad\text{almost surely.}$$
--
--   The dual weights therefore grow more slowly than $T\gamma_T$. Since $w^{(T+1)}_j/\gamma_T$ bounds the accumulated service shortfall of customer $j$, this gives the service half (28) of Theorem 3.
--
--   **Formalization Note.** The iterates are nonnegative, so "$\limsup=0$" is stated as convergence to $0$. The page's $w^{(T+1)}$ is the Lean iterate at index $T$. The lemma is stated inside the proof of Theorem 3 and uses its hypotheses, including the step size; it is posed with them. All horizons read one i.i.d. sequence, and the measurability and boundedness hypotheses are those of the other milestones.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 54, Lemma 6

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm

namespace PooledRationing.MaxWeighted

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_6
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
    (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (hfeas : PooledRationing.AsymFeas.IsFeasible F R β P c)
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → (Fin n → ℝ)) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (ϵ : ℝ) (hϵ : ϵ ∈ Set.Ioo 0 (1 / 2)) :
    ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) T j / (T * stepSize ϵ T))
      atTop (𝓝 0) := by sorry

end PooledRationing.MaxWeighted
