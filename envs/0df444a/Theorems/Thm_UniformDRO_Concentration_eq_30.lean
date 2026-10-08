-- Prove2me | Theorems.Thm_UniformDRO_Concentration_eq_30
-- name    : UniformDRO.Concentration.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:51.512981+00:00
-- url     : https://prove2.me/theorems/663c46fa-b27e-43b4-b37a-769f20a4becf
-- title:
--   (30) (corrected), p. 39 — w.p. ≥ 1 − 2e^{−t}, |g_k(η; P̂ₙ) − g_k(η; P₀)| ≤ n^{−1/(k*∨2)} M c_k (c_k/(c_k−1) ∨ 2)(√(2t) + 2/k)
-- statement:
--   In the setting of (28) — $X_1,\dots,X_n$ i.i.d. $P_0$ with $n\ge1$, $Z:\mathcal X\to[0,M]$ measurable with $M\ge1$, $k>1$, $\rho>0$, $k_*=k/(k-1)$, $c_k=(1+k(k-1)\rho)^{1/k}$, and $g_k(\eta;P)=c_k\,\mathbb E_P[(Z-\eta)_+^{k_*}]^{1/k_*}+\eta$ — for every fixed $\eta\in[-\frac1{c_k-1}M,M]$ and every $t>0$, with probability at least $1-2e^{-t}$,
--   $$
--   \big|g_k(\eta;\widehat P_n)-g_k(\eta;P_0)\big|\le n^{-1/(k_*\vee2)}\,M\,c_k\Big(\frac{c_k}{c_k-1}\vee2\Big)\Big(\sqrt{2t}+\frac2k\Big)=:\epsilon_t .
--   $$
--
--   This is the pointwise (fixed-$\eta$) concentration of the plug-in dual objective, which the union bound over a grid of $\eta$ turns into concentration of the robust risk.
--
--   **Formalization Note** The page prints the probability as $1-2e^{-2t}$. The argument gives $1-2e^{-t}$: (28) holds with probability $1-2e^{-t}$ and the bias bound from Lemma 8 is deterministic; the union bound on p. 40 also uses $e^{-t}$. The statement here is the corrected one. The failure event is bounded as an outer measure under $P_0^{\otimes n}$; $M\ge1$ is the standing assumption of Section 4 and measurability of $Z$ is added.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 2, App. C.1, eq. (30), p. 39 (corrected: 2e^{−t} for 2e^{−2t})

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- Display (30) (Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 2, App. C.1, p. 39),
corrected: for a fixed `η ∈ [-M/(c_k - 1), M]`, with probability at least `1 - 2e^{-t}`,
`|g_k(η; P̂_n) - g_k(η; P₀)| ≤ n^{-1/(k* ∨ 2)} M c_k (c_k/(c_k - 1) ∨ 2)(√(2t) + 2/k) =: ε_t`.
The page prints `1 - 2e^{-2t}`; (28) holds with `1 - 2e^{-t}` and the bias bound is
deterministic, so `1 - 2e^{-t}` is what the argument gives. Outer-measure failure event. -/
theorem eq_30 {X : Type*} [MeasurableSpace X] (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (Z : X → ℝ) (hZm : Measurable Z) (M : ℝ) (hM : 1 ≤ M) (hZ : ∀ x, Z x ∈ Set.Icc 0 M)
    (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (η : ℝ) (hη : η ∈ Set.Icc (-(M / (ck k ρ - 1))) M) :
    (Measure.pi fun _ : Fin n => P₀)
        {s | (n : ℝ) ^ (-(1 / max (kstar k) 2)) * M * ck k ρ * max (ck k ρ / (ck k ρ - 1)) 2 *
              (Real.sqrt (2 * t) + 2 / k) <
            |dualObjective k ρ (empiricalMeasure s) Z η - dualObjective k ρ P₀ Z η|} ≤
      ENNReal.ofReal (2 * Real.exp (-t)) := by sorry

end UniformDRO.Concentration
