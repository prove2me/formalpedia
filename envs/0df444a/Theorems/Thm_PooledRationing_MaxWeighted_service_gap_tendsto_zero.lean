-- Prove2me | Theorems.Thm_PooledRationing_MaxWeighted_service_gap_tendsto_zero
-- name    : PooledRationing.MaxWeighted.service_gap_tendsto_zero
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T21:36:43.06935+00:00
-- url     : https://prove2.me/theorems/1c8efe02-5cf3-443c-b4a8-beaf36be491c
-- title:
--   Proof of Theorem 3, (28), p. 53–54 — averaged expected minus realized service tends to 0 a.s.
-- statement:
--   Work under Assumptions 1 and 3 with $R_j\ge0$ jointly measurable and $s\le D$ on $P(c,D)$ for $D\ge0$. Let $w\mapsto\varphi_w$ be a selection of optimal solutions of (16) that is jointly measurable in $(w,D)$. Let $D^{(1)},D^{(2)},\dots$ be independent random demand vectors with law $F$. For a horizon $T$, let $w^{(t)}$ be the iterates (26) of Algorithm 1 run with step $\gamma_T=T^{-(1/2+\epsilon)}$, $\epsilon\in(0,1/2)$. Then for every customer $j$, almost surely
--   $$\lim_{T\to\infty}\frac1T\sum_{t=1}^T\Big(E_{\tilde D}\big[R_j(s_j(\varphi_{w^{(t)}},c,\tilde D),\tilde D_j)\big]-R_j\big(s_j(\varphi_{w^{(t)}},c,D^{(t)}),D^{(t)}_j\big)\Big)=0 .$$
--
--   In words, the average expected service of customer $j$ along the iterates equals the average realized service along the sample path, up to $o(1)$ almost surely. In the proof of (28) of Theorem 3, the realized services are controlled by the update rule: $\sum_t(\beta_j-R_j^{(t)})\le w^{(T+1)}_j/\gamma_T$. This lemma transfers that bound to the expected services that appear in (28). For each $T$ the summands are bounded martingale differences (bounded by $C$ by Assumption 3), but they depend on $T$ through $\gamma_T$. The proof is therefore the Azuma/Borel–Cantelli argument (Lemmas 4 and 5) for a triangular array, as in the proof of $\gamma_T\sum_tL_t\to0$.
--
--   **Formalization Note.** All horizons read the first $T$ entries of one i.i.d. sequence. Indices are 0-based: the Lean sum over $t=0,\dots,T-1$ is the page's sum over $t=1,\dots,T$. The expectation $E_{\tilde D}$ is taken over a fresh demand with the iterate fixed (`detService`). The hypotheses are exactly those of the milestone `gamma_sum_L_tendsto_zero`.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), proof of Theorem 3, pp. 52-54 (proof of (28), p. 53-54)

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm

namespace PooledRationing.MaxWeighted

open MeasureTheory ProbabilityTheory Filter Topology

theorem service_gap_tendsto_zero
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
    ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (PooledRationing.AsymFeas.detService F R
            (sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)) j -
          R j (((sel (mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) t)).toFun (Dseq t ω)).1 j)
            (Dseq t ω j)))
      atTop (𝓝 0) := by sorry

end PooledRationing.MaxWeighted
