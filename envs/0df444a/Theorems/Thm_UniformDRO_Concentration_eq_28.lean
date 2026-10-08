-- Prove2me | Theorems.Thm_UniformDRO_Concentration_eq_28
-- name    : UniformDRO.Concentration.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:48.946264+00:00
-- url     : https://prove2.me/theorems/13db2d05-a65a-4f5b-8a0c-1284d9e600ce
-- title:
--   (28), p. 39 — w.p. ≥ 1 − 2e^{−t}, |g_k(η; P̂ₙ) − E g_k(η; P̂ₙ)| ≤ √(2t) c_k (c_k/(c_k−1) ∨ 2) M n^{−1/(k*∨2)}
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be i.i.d. with law $P_0$ on $(\mathcal X,\mathcal A)$ and let $\widehat P_n$ be their empirical measure. Let $Z:\mathcal X\to[0,M]$ be measurable, with $M\ge1$, let $k>1$, $\rho>0$, $k_*=k/(k-1)$, $c_k=(1+k(k-1)\rho)^{1/k}$, and let $g_k(\eta;P)=c_k\,\mathbb E_P[(Z-\eta)_+^{k_*}]^{1/k_*}+\eta$. For every fixed $\eta\in[-\frac{1}{c_k-1}M,M]$ and every $t>0$, with probability at least $1-2e^{-t}$,
--   $$
--   \big|g_k(\eta;\widehat P_n)-\mathbb E_{P_0}[g_k(\eta;\widehat P_n)]\big|\le\sqrt{2t}\,c_k\Big(\frac{c_k}{c_k-1}\vee2\Big)M\,n^{-1/(k_*\vee2)} .
--   $$
--
--   This is the fluctuation half of the pointwise concentration of the plug-in dual objective; the bias half is Lemma 8.
--
--   **Formalization Note** The sample is a point of $\mathcal X^n$ under the product measure $P_0^{\otimes n}$, and $\mathbb E_{P_0}[g_k(\eta;\widehat P_n)]$ is the integral over that product of the bounded measurable map $s\mapsto g_k(\eta;\widehat P_n(s))$. The probability of the failure event is bounded as an outer measure. $M\ge1$ is the standing assumption of Section 4 (p. 19); measurability of $Z$ is added (the loss is a random variable).
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 2, App. C.1, eq. (28), p. 39

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- Display (28) (Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 2, App. C.1, p. 39):
for `X₁, …, X_n` i.i.d. `P₀`, a measurable loss `Z ∈ [0, M]` and a fixed
`η ∈ [-M/(c_k - 1), M]`, with probability at least `1 - 2e^{-t}`,
`|g_k(η; P̂_n) - E[g_k(η; P̂_n)]| ≤ √(2t) c_k (c_k/(c_k - 1) ∨ 2) M n^{-1/(k* ∨ 2)}`.
The failure event is bounded in outer measure. `M ≥ 1` is the standing assumption of §4 (p. 19). -/
theorem eq_28 {X : Type*} [MeasurableSpace X] (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (Z : X → ℝ) (hZm : Measurable Z) (M : ℝ) (hM : 1 ≤ M) (hZ : ∀ x, Z x ∈ Set.Icc 0 M)
    (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (η : ℝ) (hη : η ∈ Set.Icc (-(M / (ck k ρ - 1))) M) :
    (Measure.pi fun _ : Fin n => P₀)
        {s | Real.sqrt (2 * t) * ck k ρ * max (ck k ρ / (ck k ρ - 1)) 2 * M *
              (n : ℝ) ^ (-(1 / max (kstar k) 2)) <
            |dualObjective k ρ (empiricalMeasure s) Z η -
              ∫ s', dualObjective k ρ (empiricalMeasure s') Z η
                ∂(Measure.pi fun _ : Fin n => P₀)|} ≤
      ENNReal.ofReal (2 * Real.exp (-t)) := by sorry

end UniformDRO.Concentration
