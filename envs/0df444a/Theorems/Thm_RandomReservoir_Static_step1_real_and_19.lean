-- Prove2me | Theorems.Thm_RandomReservoir_Static_step1_real_and_19
-- name    : RandomReservoir.Static.step1_real_and_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:26:09.719644+00:00
-- url     : https://prove2.me/theorems/e11f016b-702b-4f53-ad39-03a98458b08d
-- title:
--   Proof of Theorem 1, Step 1, p. 39 — ∫ i⟨v,w⟩ μ̂(dw) is real and (19) holds, for every v ∈ 𝒳
-- statement:
--   Let $\mathcal X$ be a separable real Hilbert space, $M>0$, and $H^*:\mathcal X\to\mathbb R$. Let $\hat\mu$ be a complex measure on $\mathcal X$, written in polar form $\hat\mu(dw)=h(w)\,\nu(dw)$, where $\nu=|\hat\mu|$ is a finite measure on $\mathcal X$ and $h$ is measurable with $|h(w)|=1$. Assume
--   $$H^*(z)=\int_{\mathcal X}e^{i\langle w,z\rangle}\,\hat\mu(dw)\qquad\text{for all }z\in\mathcal X\text{ with }\|z\|\le M,$$
--   and (15): $\int_{\mathcal X}\max(1,\|w\|^2)\,\nu(dw)<\infty$. Put $\bar h(w)=2\operatorname{Re}h(w)-\operatorname{Im}h(w)$ and $\sigma(x)=\max(x,0)$. Then for every $v\in\mathcal X$:
--
--   1. the integral $\int_{\mathcal X}i\langle v,w\rangle\,\hat\mu(dw)$ is a real number;
--   2. the function $w\mapsto\int_0^1\big[\sigma(\langle v,w\rangle+u)-\sigma(-\langle v,w\rangle-u)\big]\bar h(w)\,du$ is $\nu$-integrable;
--   3. (19) holds:
--   $$\int_{\mathcal X}i\langle v,w\rangle\,\hat\mu(dw)+H^*(0)=\int_{\mathcal X}\int_0^1\big[(\langle v,w\rangle+u)^+-(-\langle v,w\rangle-u)^+\big]\big(2\operatorname{Re}h(w)-\operatorname{Im}h(w)\big)\,du\,|\hat\mu|(dw).$$
--
--   This is the linear part of the integral representation (20) of $H^*$ by ReLU units. It is the analogue for a Hilbert space of (10) in the proof of Proposition 2.
--
--   **Formalization Note.** This is the case $m=1$ of Theorem 1; the proof reduces to it. The complex measure is in polar form (Rudin, Thm 6.12, quoted on p. 39). The claim holds for every $v$, not only for $\|v\|\le M$: the realness argument evaluates $H^*$ at $\lambda v$ for small $\lambda>0$.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Proof of Theorem 1, Step 1, p. 39, from "We claim" to (19)

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory

/-- Proof of Theorem 1, Step 1, p. 39 (Gonon–Grigoryeva–Ortega, Ann. Appl. Probab. 33 (2023)), the
claim before (19) and (19) itself, for one component (`m = 1`): if the real function `H*` is
represented on the ball `‖z‖ ≤ M` by the complex measure `μ̂ = h·ν` (`ν = |μ̂|`, `|h| = 1`) satisfying
(15), then for every `v ∈ 𝒳` the integral `∫ i⟨v,w⟩ μ̂(dw)` is real, and
`∫ i⟨v,w⟩ μ̂(dw) + H*(0) = ∫∫_0^1 [(⟨v,w⟩+u)^+ − (−⟨v,w⟩−u)^+] h̄(w) du ν(dw)` with
`h̄ = 2 Re h − Im h`; the inner integrand is `ν`-integrable. -/
theorem step1_real_and_19
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (M : ℝ) (hM : 0 < M) (Hstar : 𝒳 → ℝ)
    (ν : Measure 𝒳) [IsFiniteMeasure ν]
    (h : 𝒳 → ℂ) (hh_meas : Measurable h) (hh_norm : ∀ w, ‖h w‖ = 1)
    (hrep : ∀ z : 𝒳, ‖z‖ ≤ M →
      (Hstar z : ℂ) = ∫ w, Complex.exp (Complex.I * (inner ℝ w z : ℝ)) * h w ∂ν)
    (h15 : ∫⁻ w, ENNReal.ofReal (max 1 (‖w‖ ^ 2)) ∂ν < ⊤) (v : 𝒳) :
    (∫ w, Complex.I * (inner ℝ v w : ℝ) * h w ∂ν).im = 0 ∧
    Integrable (fun w => ∫ u in (0 : ℝ)..1,
        (relu (inner ℝ v w + u) - relu (-(inner ℝ v w) - u)) * hbar h w) ν ∧
    (∫ w, Complex.I * (inner ℝ v w : ℝ) * h w ∂ν) + (Hstar 0 : ℂ) =
      ((∫ w, (∫ u in (0 : ℝ)..1,
        (relu (inner ℝ v w + u) - relu (-(inner ℝ v w) - u)) * hbar h w) ∂ν : ℝ) : ℂ) := by sorry

end RandomReservoir.Static
