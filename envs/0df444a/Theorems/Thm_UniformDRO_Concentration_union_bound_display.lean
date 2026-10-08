-- Prove2me | Theorems.Thm_UniformDRO_Concentration_union_bound_display
-- name    : UniformDRO.Concentration.union_bound_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:12.377975+00:00
-- url     : https://prove2.me/theorems/630b3577-7a22-4c7d-a506-e9e3e8f63628
-- title:
--   Proof of Theorem 2, p. 40 — w.p. ≥ 1 − 2exp(−t + log((c_k/(c_k−1))M/ε_{t,n})), |R_k(Z; P̂ₙ) − R_k(Z; P₀)| ≤ (2c_k + 3)ε_{t,n}
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be i.i.d. with law $P_0$ and empirical measure $\widehat P_n$, let $Z:\mathcal X\to[0,M]$ be measurable with $M\ge1$, $k>1$, $\rho>0$, $k_*=k/(k-1)$ and $c_k=(1+k(k-1)\rho)^{1/k}$. For $t>0$ put
--   $$
--   \epsilon_{t,n}=n^{-1/(k_*\vee2)}\,M\,c_k\Big(\frac{c_k}{c_k-1}\vee2\Big)\Big(\sqrt{2t}+\frac2k\Big).
--   $$
--   Then, with probability at least $1-2\exp\big(-t+\log\big(\frac{c_k}{c_k-1}\frac{M}{\epsilon_{t,n}}\big)\big)$,
--   $$
--   \big|\mathcal R_k(Z;\widehat P_n)-\mathcal R_k(Z;P_0)\big|\le(2c_k+3)\,\epsilon_{t,n} ,
--   $$
--   where $\mathcal R_k$ is the Cressie–Read robust risk of radius $\rho$.
--
--   This is the uniform-in-$\eta$ version of (30), obtained from a grid of the interval of Lemma 9; a change of variables in $t$ turns it into Theorem 2.
--
--   **Formalization Note** The failure event is bounded as an outer measure under $P_0^{\otimes n}$. When $\frac{c_k}{c_k-1}\frac{M}{\epsilon_{t,n}}<1$ the stated failure probability is below $2e^{-t}$, but then $(2c_k+3)\epsilon_{t,n}>M\ge|\mathcal R_k(Z;\widehat P_n)-\mathcal R_k(Z;P_0)|$, so the event is empty and the statement holds for every $t>0$. $M\ge1$ is the standing assumption of Section 4; measurability of $Z$ is added.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 2, App. C.1, p. 40, the display after (30) and Lemma 9 (definition of ε_{t,n} and the final union-bound display)

import Mathlib
import Definitions.Def_UniformDRO_Concentration_RobustRisk

open MeasureTheory

namespace UniformDRO.Concentration

/-- The uniform-in-`η` display (Duchi & Namkoong, arXiv:1810.08750v6, proof of Theorem 2,
App. C.1, p. 40): with `ε_{t,n} = n^{-1/(k* ∨ 2)} M c_k (c_k/(c_k - 1) ∨ 2)(√(2t) + 2/k)`,
with probability at least `1 - 2 exp(-t + log((c_k/(c_k - 1)) M / ε_{t,n}))`,
`|R_k(Z; P̂_n) - R_k(Z; P₀)| ≤ (2c_k + 3) ε_{t,n}`. Outer-measure failure event; `M ≥ 1` is the
standing assumption of §4 (p. 19). -/
theorem union_bound_display {X : Type*} [MeasurableSpace X] (P₀ : Measure X)
    [IsProbabilityMeasure P₀] (Z : X → ℝ) (hZm : Measurable Z) (M : ℝ) (hM : 1 ≤ M)
    (hZ : ∀ x, Z x ∈ Set.Icc 0 M) (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => P₀)
        {s | (2 * ck k ρ + 3) *
              ((n : ℝ) ^ (-(1 / max (kstar k) 2)) * M * ck k ρ * max (ck k ρ / (ck k ρ - 1)) 2 *
                (Real.sqrt (2 * t) + 2 / k)) <
            |robustRisk k ρ (empiricalMeasure s) Z - robustRisk k ρ P₀ Z|} ≤
      ENNReal.ofReal (2 * Real.exp (-t + Real.log (ck k ρ / (ck k ρ - 1) * M /
        ((n : ℝ) ^ (-(1 / max (kstar k) 2)) * M * ck k ρ * max (ck k ρ / (ck k ρ - 1)) 2 *
          (Real.sqrt (2 * t) + 2 / k))))) := by sorry

end UniformDRO.Concentration
