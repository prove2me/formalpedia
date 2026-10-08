-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_kingman_subadditive
-- name    : PalmQueueing.Ergodic.kingman_subadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:57:25.57195+00:00
-- url     : https://prove2.me/theorems/e1fc569d-b0bf-4f66-a58a-3deb01d0c9a9
-- title:
--   Theorem 1.6.2 — Kingman's sub-additive ergodic theorem
-- statement:
--   **Theorem 1.6.2 (Sub-additive ergodic theorem).** Let $(\Omega,\mathcal{F},P^0)$ be a
--   probability space and $\theta$ be a discrete ergodic flow on this space. Let $\{h_n\}_{n\in
--   \mathbb{N}^*}$ be a sub-additive sequence of measurable mappings from $(\Omega,\mathcal{F})$ to
--   $(\mathbb{R},\mathcal{B})$. If $h_1^+ = \max(h_1, 0)$ is in $L^1(P^0)$, then
--   $$ \exists \lim_{n\to\infty} \frac{1}{n}h_n = \bar h, \qquad P^0\text{-a.s.}, \tag{1.6.2} $$
--   where $\bar h$ is some constant in $\mathbb{R}\cup\{-\infty\}$. In addition,
--   $$ \lim_{n\to\infty} \frac{1}{n}E^0[h_n] = \inf_n \frac{1}{n}E^0[h_n] = \bar h . \tag{1.6.3} $$
--
--   This is **Kingman's theorem**, which the book quotes rather than proves: "For a proof, see Kingman
--   (1976)."
--
--   Three assertions, all stated. The limit **exists** a.s.; it is a **constant**, which is what
--   ergodicity buys and why the conclusion is about a single $\bar h$ rather than a random variable;
--   and (1.6.3) identifies that constant as the **infimum** of the means, not merely as their limit.
--
--   $\bar h$ lives in $\mathbb{R}\cup\{-\infty\}$, so $-\infty$ is a genuine possible value. That is
--   exactly why Theorem 2.11.2 of this series' mission III has to assume the one-sided bound
--   $E[X^{[0]}_n] > -Cn$ when it applies this theorem.
--
--   Mathlib has no sub-additive ergodic theorem and neither does the platform.
--
--   One correction to the page: it prints the integrability hypothesis as $h_1^+ = \max(g_1, 0)$, with
--   $g_1$ where the sub-additive sequence is $\{h_n\}$ — $g$ being the letter used two paragraphs above
--   for the *additive* case. It is stated here with $h_1$, which is what makes the hypothesis about
--   the sequence the theorem is about.
--
--   **Formalization Note.** A discrete flow is, by the book's definition on p.46, "a bijective and measurable map from $\Omega$ to itself, which preserves $P^0$"; the statement carries `Function.Bijective θ` alongside Mathlib's `Ergodic θ P0` (measure preserving and pre-ergodic). The means $E^0[h_n]$ are extended reals, computed as $\int h_n^+\,dP^0 - \int h_n^-\,dP^0$ in `EReal` (finite minus possibly $+\infty$, since $h_n^+ \in L^1$ by sub-additivity): $E^0[h_n] = -\infty$ is exactly the case $\bar h = -\infty$, which a Bochner integral would turn into $0$. The conclusion also records $\bar h \ne +\infty$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 48, Theorem 1.6.2

import Mathlib
import Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow

/-!
# Theorem 1.6.2: Kingman's sub-additive ergodic theorem (§1.6.1, p.48)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.6.2 (Sub-additive ergodic theorem)** (p.48). Let `(Ω, F, P⁰)` be a probability
space and `θ` be a discrete ergodic flow on this space. Let `{h_n}_{n ∈ ℕ*}` be a sub-additive
sequence of measurable mappings from `(Ω, F)` to `(ℝ, B)`. If `h_1⁺ = max(h_1, 0)` is in
`L¹(P⁰)`, then

`(1.6.2)  ∃ lim_{n→∞} (1/n) h_n = h̄,  P⁰-a.s.`

where `h̄` is some constant in `ℝ ∪ {−∞}`. In addition,

`(1.6.3)  lim_{n→∞} (1/n) E⁰[h_n] = inf_n (1/n) E⁰[h_n] = h̄`.

**This is Kingman's theorem, which the book quotes rather than proves**: "For a proof, see Kingman
(1976)."

Three things are asserted and all three are stated. The limit **exists** a.s.; it is a
**constant**, which is what ergodicity buys and which is why the conclusion is about a single
`h̄ : EReal` rather than a random variable; and `(1.6.3)` identifies that constant as the
**infimum** of the means, not merely as their limit.

`h̄` lives in `ℝ ∪ {−∞}` and is therefore `EReal`-valued: `−∞` is a genuine possible value, which
is exactly why Theorem 2.11.2 of mission `02b` has to assume the one-sided bound
`E[X_n^{[0]}] > −Cn` when it applies this theorem.

Mathlib has no sub-additive ergodic theorem — no `Kingman`, no sub-additive file under
`Dynamics/` — and neither does the platform.

The page prints the integrability hypothesis as `h_1⁺ = max(g_1, 0)`, with `g_1` where the
sub-additive sequence is `{h_n}`; `g` is the letter used two paragraphs above for the *additive*
case. It is stated here with `h_1`, which is what makes the hypothesis about the sequence the
theorem is about.

`hbij` is the book's definition of a discrete flow (p.46). `E⁰[h_n]` is written as the extended
real `∫⁻ h_n⁺ − ∫⁻ h_n⁻`, not as a Bochner integral: `h_n⁺` is integrable but `h_n⁻` need not be,
and `E⁰[h_n] = −∞` is exactly the case `h̄ = −∞`, which a Bochner integral would silently turn
into `0`. -/
theorem kingman_subadditive (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω → Ω) (hθ : Measurable θ) (hbij : Function.Bijective θ) (herg : Ergodic θ P0)
    (h : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (h n))
    (hsub : IsSubAdditiveSeq θ P0 h)
    (hint : Integrable (fun ω => max (h 1 ω) 0) P0) :
    ∃ hbar : EReal, hbar ≠ ⊤ ∧
      (∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => ((h n ω / (n : ℝ) : ℝ) : EReal)) atTop (𝓝 hbar)) ∧
      Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
          (((∫⁻ ω, ENNReal.ofReal (h n ω) ∂P0 : ENNReal) : EReal) -
            ((∫⁻ ω, ENNReal.ofReal (-h n ω) ∂P0 : ENNReal) : EReal)))
        atTop (𝓝 hbar) ∧
      hbar = ⨅ n : {n : ℕ // 1 ≤ n}, ((((n : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
          (((∫⁻ ω, ENNReal.ofReal (h (n : ℕ) ω) ∂P0 : ENNReal) : EReal) -
            ((∫⁻ ω, ENNReal.ofReal (-h (n : ℕ) ω) ∂P0 : ENNReal) : EReal)) := by sorry

end PalmQueueing.Ergodic
