-- Prove2me | Theorems.Thm_RandomReservoir_Static_eq_21
-- name    : RandomReservoir.Static.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:47.010362+00:00
-- url     : https://prove2.me/theorems/72465622-10b5-4b66-a904-8ceb18f5663e
-- title:
--   α ≪ π and (21), Proof of Theorem 1, Step 1, p. 40 — |dα/dπ(w,u)| ≤ (𝟙_{(−M‖w‖,0]}(u) + 2√2 𝟙_{[−1,1]}(u)) g(w)/π_ℝ(u)
-- statement:
--   Let $\mathcal X$ be a separable real Hilbert space, $M>0$, and let $\hat\mu(dw)=h(w)\,\nu(dw)$, where $\nu=|\hat\mu|$ is a finite measure on $\mathcal X$ and $h$ is measurable with $|h(w)|=1$, with (15): $\int\max(1,\|w\|^2)\,\nu(dw)<\infty$. Let $\pi_{\mathcal X}$ be a probability measure on $\mathcal X$ and $\pi_{\mathbb R}\ge0$ a measurable probability density on $\mathbb R$, and $\pi=\pi_{\mathcal X}\otimes(\pi_{\mathbb R}(x)dx)$. Assume $\nu+\nu^-\ll\pi_{\mathcal X}$ and that condition (i) or (ii) of Theorem 1 holds. Let $\alpha$ be the signed measure of (20) and $g=\frac{d(\nu+\nu^-)}{d\pi_{\mathcal X}}$.
--
--   Then $\alpha\ll\pi$. More precisely, there is a measurable, $\pi$-integrable $\varphi=\frac{d\alpha}{d\pi}$ with $\alpha(S)=\int_S\varphi\,d\pi$ for every measurable $S\subseteq\mathcal X\times\mathbb R$, and for $\pi$-almost every $(w,u)$
--   $$\Big|\frac{d\alpha}{d\pi}(w,u)\Big|\le\Big(\mathbb 1_{(-M\|w\|,0]}(u)+2\sqrt2\,\mathbb 1_{[-1,1]}(u)\Big)\frac{1}{\pi_{\mathbb R}(u)}\,g(w).\tag{21}$$
--
--   The density $\varphi$ is the importance weight of Step 2: $V_i=\varphi(A_i,\zeta_i)$. The bound (21) controls its second moment in (26).
--
--   **Formalization Note.** The statement is for $m=1$. "$\alpha(S)$" is $\int_S k_+\,d(\nu\otimes du)+\int_S k_-\,d(\nu^-\otimes du)$ with the densities of the definition file. Both are integrable under (15). The bound is required $\pi$-a.e. because $d\alpha/d\pi$ is defined only up to $\pi$-null sets.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Proof of Theorem 1, Step 1, p. 40, from "Finally, let A" to (21)

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory

/-- α ≪ π and (21), Proof of Theorem 1, Step 1, p. 40 (Gonon–Grigoryeva–Ortega, Ann. Appl. Probab.
33 (2023)), for one component. The signed measure `α = α₁ + α₂` has density `kPlus M h` with respect
to `ν(dw) du` and `kMinus M h` with respect to `ν⁻(dw) du` (`ν = |μ̂|`). Under the hypotheses of
Theorem 1, `α` is absolutely continuous with respect to `π = π_𝒳 ⊗ (π_ℝ(x) dx)`: there is a
`π`-integrable density `φ = dα/dπ` with `α(S) = ∫_S φ dπ` for every measurable `S`, and
`|φ(w,u)| ≤ (𝟙_{(−M‖w‖,0]}(u) + 2√2 𝟙_{[−1,1]}(u)) g(w)/π_ℝ(u)` for `π`-a.e. `(w,u)`, where
`g = d(ν + ν⁻)/dπ_𝒳`. -/
theorem eq_21
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (M : ℝ) (hM : 0 < M)
    (ν : Measure 𝒳) [IsFiniteMeasure ν]
    (h : 𝒳 → ℂ) (hh_meas : Measurable h) (hh_norm : ∀ w, ‖h w‖ = 1)
    (h15 : ∫⁻ w, ENNReal.ofReal (max 1 (‖w‖ ^ 2)) ∂ν < ⊤)
    (πX : Measure 𝒳) [IsProbabilityMeasure πX]
    (πR : ℝ → ℝ) (hπR_meas : Measurable πR) (hπR_nn : ∀ x, 0 ≤ πR x)
    (hπR_one : ∫ x, πR x = 1)
    (hac : ν + ν.map (fun w => -w) ≪ πX)
    (hcase : SamplingCondition M πX πR) :
    ∃ φ : 𝒳 × ℝ → ℝ, Measurable φ ∧ Integrable φ (samplingLaw πX πR) ∧
      (∀ S : Set (𝒳 × ℝ), MeasurableSet S →
        ∫ p in S, φ p ∂(samplingLaw πX πR) =
          (∫ p in S, kPlus M h p ∂(ν.prod volume))
            + ∫ p in S, kMinus M h p ∂((ν.map (fun w => -w)).prod volume)) ∧
      ∀ᵐ p ∂(samplingLaw πX πR),
        |φ p| ≤ (Set.indicator (Set.Ioc (-(M * ‖p.1‖)) 0) (fun _ => (1 : ℝ)) p.2
            + 2 * Real.sqrt 2 * Set.indicator (Set.Icc (-1) 1) (fun _ => (1 : ℝ)) p.2)
          * (1 / πR p.2) * gdens ν πX p.1 := by sorry

end RandomReservoir.Static
