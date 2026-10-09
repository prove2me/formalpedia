-- Prove2me | Theorems.Thm_RandomReservoir_Static_eq_20
-- name    : RandomReservoir.Static.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:28.636639+00:00
-- url     : https://prove2.me/theorems/d36a7343-f897-4144-aa5c-95812bef394d
-- title:
--   (20), Proof of Theorem 1, Step 1, p. 40 — H*(v) = ∫ σ(⟨v,w⟩ + u) α(dw,du) for ‖v‖ ≤ M
-- statement:
--   Let $\mathcal X$, $M>0$, $H^*:\mathcal X\to\mathbb R$ and the complex measure $\hat\mu(dw)=h(w)\,\nu(dw)$, where $\nu=|\hat\mu|$ is a finite measure on $\mathcal X$ and $h$ is measurable with $|h(w)|=1$ be as in Theorem 1 with $m=1$: $H^*(z)=\int e^{i\langle w,z\rangle}\hat\mu(dw)$ for $\|z\|\le M$, and (15) holds. Put $\bar h=2\operatorname{Re}h-\operatorname{Im}h$, $\nu^-(\cdot)=\nu(-\cdot)$, and let $\alpha=\alpha_1+\alpha_2$ be the signed measure on $\mathcal X\times\mathbb R$ with
--   $$\alpha_1(dw,du)=-\mathbb 1_{(-M\|w\|,0]}(u)\big[\operatorname{Re}[e^{-iu}h(w)]\,\nu(dw)\,du+\operatorname{Re}[e^{iu}h(-w)]\,\nu^-(dw)\,du\big],$$
--   $$\alpha_2(dw,du)=\mathbb 1_{[0,1]}(u)\bar h(w)\,\nu(dw)\,du-\mathbb 1_{[-1,0]}(u)\bar h(-w)\,\nu^-(dw)\,du.$$
--   Then for every $v\in\mathcal X$ with $\|v\|\le M$, the integrand $\sigma(\langle v,w\rangle+u)$ is integrable against both parts of $\alpha$ and
--   $$H^*(v)=\int_{\mathcal X\times\mathbb R}\sigma(\langle v,w\rangle+u)\,\alpha(dw,du).$$
--
--   This is the integral representation of $H^*$ on the ball $B_M$ by ReLU units, which Step 2 turns into a Monte Carlo estimator.
--
--   **Formalization Note.** $\alpha$ is written through its densities: $k_+$ (`kPlus`) with respect to $\nu\otimes du$ and $k_-$ (`kMinus`) with respect to $\nu^-\otimes du$. The two integrability conjuncts guarantee that the identity is not between default values of non-integrable Bochner integrals.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Proof of Theorem 1, Step 1, p. 40, (20)

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory

/-- (20), Proof of Theorem 1, Step 1, p. 40 (Gonon–Grigoryeva–Ortega, Ann. Appl. Probab. 33 (2023)),
for one component: with `α = α₁ + α₂`, which has density `kPlus M h` with respect to `|μ̂|(dw) du` and
density `kMinus M h` with respect to `|μ̂|⁻(dw) du`, every `v` with `‖v‖ ≤ M` satisfies
`H*(v) = ∫ σ(⟨v,w⟩ + u) α(dw, du)`; both integrands are integrable. -/
theorem eq_20
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (M : ℝ) (hM : 0 < M) (Hstar : 𝒳 → ℝ)
    (ν : Measure 𝒳) [IsFiniteMeasure ν]
    (h : 𝒳 → ℂ) (hh_meas : Measurable h) (hh_norm : ∀ w, ‖h w‖ = 1)
    (hrep : ∀ z : 𝒳, ‖z‖ ≤ M →
      (Hstar z : ℂ) = ∫ w, Complex.exp (Complex.I * (inner ℝ w z : ℝ)) * h w ∂ν)
    (h15 : ∫⁻ w, ENNReal.ofReal (max 1 (‖w‖ ^ 2)) ∂ν < ⊤)
    (v : 𝒳) (hv : ‖v‖ ≤ M) :
    Integrable (fun p : 𝒳 × ℝ => relu (inner ℝ v p.1 + p.2) * kPlus M h p)
        (ν.prod volume) ∧
    Integrable (fun p : 𝒳 × ℝ => relu (inner ℝ v p.1 + p.2) * kMinus M h p)
        ((ν.map (fun w => -w)).prod volume) ∧
    Hstar v = (∫ p, relu (inner ℝ v p.1 + p.2) * kPlus M h p ∂(ν.prod volume))
      + ∫ p, relu (inner ℝ v p.1 + p.2) * kMinus M h p ∂((ν.map (fun w => -w)).prod volume) := by sorry

end RandomReservoir.Static
