-- Prove2me | Theorems.Thm_RandomReservoir_Static_eq_26
-- name    : RandomReservoir.Static.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:59.567216+00:00
-- url     : https://prove2.me/theorems/9c1b4414-6c7d-44bf-84cc-f22db84c29bb
-- title:
--   (26), Proof of Theorem 1, Step 2, p. 41 — E[V₁² σ(⟨A₁,z⟩+ζ₁)²] ≤ C* for ‖z‖ ≤ M (constant 32·max(M², 1))
-- statement:
--   Let $\mathcal X$ be a separable real Hilbert space, $M>0$, $\nu$ a finite measure on $\mathcal X$, $\pi_{\mathcal X}$ a probability measure on $\mathcal X$ and $\pi_{\mathbb R}\ge0$ a measurable probability density on $\mathbb R$, and $\pi=\pi_{\mathcal X}\otimes(\pi_{\mathbb R}(x)dx)$. Assume $\nu+\nu^-\ll\pi_{\mathcal X}$, condition (i) or (ii) of Theorem 1, and (16) for $g=\frac{d(\nu+\nu^-)}{d\pi_{\mathcal X}}$:
--   $$\int_{\mathcal X}F_\pi(M\|w\|)\|w\|^2g(w)^2\,\pi_{\mathcal X}(dw)<\infty,\qquad\int_{\mathcal X}\max(\|w\|^2,1)g(w)^2\,\pi_{\mathcal X}(dw)<\infty.$$
--   Let $\varphi$ be measurable and satisfy the bound (21) $\pi$-almost everywhere. Then for every $z\in\mathcal X$ with $\|z\|\le M$
--   $$\int_{\mathcal X\times\mathbb R}\varphi(w,u)^2\,\sigma(\langle w,z\rangle+u)^2\,\pi(dw,du)\le M^2\!\int_{\mathcal X}F_\pi(M\|w\|)\|w\|^2g(w)^2\,\pi_{\mathcal X}(dw)+32\max(M^2,1)\big(F_\pi(1)-F_\pi(-1)\big)\!\int_{\mathcal X}\max(\|w\|^2,1)g(w)^2\,\pi_{\mathcal X}(dw)=C^*.$$
--
--   With $V_1=\varphi(A_1,\zeta_1)$ the left side is $\mathbb E[V_1^2\sigma(\langle A_1,z\rangle+\zeta_1)^2]$, so together with (25) this gives the rate $C^*/N$ of Theorem 1.
--
--   **Formalization Note.** The statement is for $m=1$. The coefficient is $32\max(M^2,1)$, not the printed $32M^2$. The proof's line (26) gives $2\cdot16(|\langle w,z\rangle|^2+1)\int_{-1}^1\pi_{\mathbb R}^{-1}=16(M^2\|w\|^2+1)(F_\pi(1)-F_\pi(-1))$, and the printed bound by $32M^2\max(\|w\|^2,1)(\dots)$ needs $M\ge1$; for $M\ge1$ the two coincide. The left side is a lower Lebesgue integral, so it cannot vanish by non-integrability.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Proof of Theorem 1, Step 2, p. 41, (26)

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory

/-- (26), Proof of Theorem 1, Step 2, p. 41 (Gonon–Grigoryeva–Ortega, Ann. Appl. Probab. 33 (2023)),
for one component, with `32·max(M², 1)` in place of the printed `32 M²`: if `φ` satisfies the bound
(21) `π`-a.e., then for every `z` with `‖z‖ ≤ M`,
`E[V_1² σ(⟨A_1,z⟩ + ζ_1)²] = ∫ φ(w,u)² σ(⟨w,z⟩ + u)² π(dw,du) ≤ C*`. -/
theorem eq_26
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (M : ℝ) (hM : 0 < M)
    (ν : Measure 𝒳) [IsFiniteMeasure ν]
    (πX : Measure 𝒳) [IsProbabilityMeasure πX]
    (πR : ℝ → ℝ) (hπR_meas : Measurable πR) (hπR_nn : ∀ x, 0 ≤ πR x)
    (hπR_one : ∫ x, πR x = 1)
    (hac : ν + ν.map (fun w => -w) ≪ πX)
    (hcase : SamplingCondition M πX πR)
    (h16a : Integrable (fun w => Fπ πR (M * ‖w‖) * ‖w‖ ^ 2 * gdens ν πX w ^ 2) πX)
    (h16b : Integrable (fun w => max (‖w‖ ^ 2) 1 * gdens ν πX w ^ 2) πX)
    (φ : 𝒳 × ℝ → ℝ) (hφ : Measurable φ)
    (h21 : ∀ᵐ p ∂(samplingLaw πX πR),
        |φ p| ≤ (Set.indicator (Set.Ioc (-(M * ‖p.1‖)) 0) (fun _ => (1 : ℝ)) p.2
            + 2 * Real.sqrt 2 * Set.indicator (Set.Icc (-1) 1) (fun _ => (1 : ℝ)) p.2)
          * (1 / πR p.2) * gdens ν πX p.1)
    (z : 𝒳) (hz : ‖z‖ ≤ M) :
    ∫⁻ p, ENNReal.ofReal (φ p ^ 2 * relu (inner ℝ p.1 z + p.2) ^ 2) ∂(samplingLaw πX πR)
      ≤ ENNReal.ofReal (CstarJ M πX πR (gdens ν πX)) := by sorry

end RandomReservoir.Static
