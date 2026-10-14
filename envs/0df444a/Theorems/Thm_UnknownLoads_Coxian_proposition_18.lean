-- Prove2me | Theorems.Thm_UnknownLoads_Coxian_proposition_18
-- name    : UnknownLoads.Coxian.proposition_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:55.819695+00:00
-- url     : https://prove2.me/theorems/195032f6-0d38-488c-a0ef-7f8699bb617b
-- title:
--   Proposition 18 — while ℓ_k = ⌊ρ⌋_Δ, the limits of the masses satisfy ẏ ≤ −η(y − Δz) when x < ⌊ρ⌋_Δ and ż ≤ −ηz
-- statement:
--   Fix $\omega \in \Omega_T$ (omitted below) and an increasing sequence $\mathcal K$ of natural numbers. Let $\eta := \min\{(1-p_m)\mu_m : 1 \le m \le r\}$, and let $x_k, y_k, z_k$ be the mass processes (22) with $\ell = \lfloor\rho\rfloor_\Delta$. Suppose that
--
--   (a) $\{s_k : k\in\mathcal K\}$ converges to a function $s$ with respect to $\varrho$ (coordinatewise uniformly on $[0,T]$), and
--
--   (b) there exist $0 \le t_0 < t_1 \le T$ with $\ell_k(t) = \lfloor\rho\rfloor_\Delta$ for all $t \in [t_0,t_1]$ and all $k \in \mathcal K$.
--
--   Then $\{x_k\}$, $\{y_k\}$, $\{z_k\}$ converge uniformly over $[0,T]$ to absolutely continuous functions $x, y, z$, and for $t \in (t_0,t_1)$:
--
--   1. if $x(t) < \lfloor\rho\rfloor_\Delta$, then
--   $$\dot y \le -\eta\,(y - \Delta z) \qquad \text{almost everywhere on a neighborhood of } t;$$
--   2. moreover,
--   $$\dot z \le -\eta\, z \qquad\text{almost everywhere on } [t_0,t_1].$$
--
--   These differential inequalities drive the proof of Theorem 3: the mass $z$ beyond the first $\lfloor\rho\rfloor_\Delta + \Delta$ columns decays exponentially at rate $\eta$, and the first $\lfloor\rho\rfloor_\Delta$ columns fill up.
--
--   **Formalization Note** $\mathcal K$ is the range of a strictly increasing $\varphi : \mathbb N\to\mathbb N$. Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval` on $[0,T]$. "$\dot y \le \dots$ almost everywhere on a neighborhood of $t$" is: there is a neighbourhood $V$ of $t$ such that for Lebesgue-almost every $\tau\in V$, `deriv y τ ≤ -η (y τ - Δ z τ)`. Lean's `deriv` is $0$ where $y$ is not differentiable, but an absolutely continuous function is differentiable almost everywhere, so the almost-everywhere statement has its intended meaning.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 42–43, Proposition 18 (η defined on p. 42)

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_NicePaths
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian

/-- Proposition 18 (pp. 42–43). Fix `ω ∈ Ω_T` and an increasing sequence `𝒦 = {φ k}`. If
(a) `s_k → s` with respect to `ϱ` along `𝒦` and (b) `ℓ_k(t) = ⌊ρ⌋_Δ` on `[t_0, t_1]` for all
`k ∈ 𝒦`, then `x_k, y_k, z_k` converge uniformly over `[0, T]` to absolutely continuous `x, y, z`,
and for `t ∈ (t_0, t_1)`: (i) if `x(t) < ⌊ρ⌋_Δ` then `ẏ ≤ -η(y - Δz)` a.e. on a neighbourhood
of `t`; (ii) `ż ≤ -ηz` a.e. on `[t_0, t_1]`, with `η = min_m (1 - p_m) μ_m`. -/
theorem proposition_18 {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (T : ℝ) (BT : ℕ) (ω : Ω) (hω : IsNicePath sys T BT ω)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (sLimPath : ℝ → Profile P.r → ℝ) (ha : RhoConverges (fun k => sys.s (φ k) ω) sLimPath T)
    (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht₀₁ : t₀ < t₁) (ht₁ : t₁ ≤ T)
    (hb : ∀ k : ℕ, ∀ t ∈ Set.Icc t₀ t₁, (sys.ℓ (φ k) ω t : ℤ) = floorDelta P.Δ (rho P)) :
    ∃ x y z : ℝ → ℝ,
      TendstoUniformlyOn (fun (k : ℕ) (t : ℝ) => xMass P (sys.s (φ k) ω t)) x atTop
        (Set.Icc 0 T) ∧
      TendstoUniformlyOn (fun (k : ℕ) (t : ℝ) => yMass P (sys.s (φ k) ω t)) y atTop
        (Set.Icc 0 T) ∧
      TendstoUniformlyOn (fun (k : ℕ) (t : ℝ) => zMass P (sys.s (φ k) ω t)) z atTop
        (Set.Icc 0 T) ∧
      AbsolutelyContinuousOnInterval x 0 T ∧ AbsolutelyContinuousOnInterval y 0 T ∧
      AbsolutelyContinuousOnInterval z 0 T ∧
      (∀ t ∈ Set.Ioo t₀ t₁, x t < (ellStar P : ℝ) →
        ∃ V ∈ 𝓝 t, ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ V →
          deriv y τ ≤ -(eta P) * (y τ - (P.Δ : ℝ) * z τ)) ∧
      (∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Icc t₀ t₁ → deriv z τ ≤ -(eta P) * z τ) := by sorry

end UnknownLoads.Coxian
