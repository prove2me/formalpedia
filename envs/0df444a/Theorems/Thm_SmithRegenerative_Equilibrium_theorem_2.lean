-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_theorem_2
-- name    : SmithRegenerative.Equilibrium.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:39.640637+00:00
-- url     : https://prove2.me/theorems/4053a34d-f16b-45ca-a51f-497b19e510c6
-- title:
--   Theorem 2 — an aperiodic equilibrium process with a certain event 𝓔 has lim P{x_t ∈ A | z} = (1/μ₁)∫₀^∞ φ_A(v){1 − F(v)}dv
-- statement:
--   Let $x_t$ be an equilibrium process $\mathcal E(\mathfrak z, \mathcal A, \{t_i\})$: a process on a state space $\mathfrak X$ with a general renewal process $t_0, t_1, \dots$ (cycle law $F$, mean $\mu_1 \in (0,\infty]$, delay laws $K_z$) such that, given a boundary condition $z$, a regeneration by time $t$ and the epoch $L_t$ of the last regeneration, $x_t \in A$ has conditional probability $\varphi_A(t - L_t)$ for every $A \in \mathcal A$. Suppose
--
--   1. $\varpi = 0$ ($\mathcal E$ is aperiodic), and
--   2. $K_z(+\infty) = 1$ for every $z$ ($\mathcal E$ is certain).
--
--   Let $z \in \mathfrak z$ and $A \in \mathcal A$, and suppose either
--
--   - (iv)$'$ $\varphi_A(t)\{1 - F(t)\}$ is integrable over $(0,\infty)$ and monotonic in $(0,\infty)$, or
--   - (iv)$''$ $\mu_1 < \infty$ and either (iv)$''_a$ $\varphi_A(t)\{1-F(t)\}$ is of bounded variation in every finite interval, or (iv)$''_b$ $F \in \mathfrak S$.
--
--   Then
--   $$
--   \lim_{t\to\infty} P\{x_t \in A \mid z\} = \frac{1}{\mu_1} \int_0^\infty \varphi_A(v)\{1 - F(v)\}\, dv,
--   $$
--   where the limit is $0$ if $\mu_1 = \infty$ (possible under (iv)$'$).
--
--   The theorem identifies the limiting state probabilities of a process that regenerates at renewal epochs: in the limit, the time since the last regeneration has density $\{1-F(v)\}/\mu_1$, and the state probability is $\varphi_A$ averaged against it.
--
--   **Formalization Note** Hypothesis (iii) is built into the definition of equilibrium process ($t_0$ is real-valued). Hypothesis (iv) concerns the one set $A$ of the conclusion. "Monotonic" means non-decreasing or non-increasing on $(0,\infty)$; "bounded variation in every finite $t$-interval" means on every $[0,b]$; $\varphi_A$ is measurable by definition. The cases $\mu_1 = \infty$ and $\mu_1 < \infty$ are separate conclusions, and $1 - F(v) = F((v,\infty))$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, pp. 14–15, Theorem 2, (3·4·2)

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

namespace SmithRegenerative.Equilibrium

open MeasureTheory Filter Topology

/-- **Theorem 2** (Smith 1955, §3·4, pp. 14–15). If (i) `x_t` is an equilibrium process
`𝓔(𝔷, 𝒜, {tᵢ})`, (ii) `ϖ = 0` (`𝓔` aperiodic), (iii) `K_z(+∞) = 1` (`𝓔` certain), then for every
`z ∈ 𝔷` and every `A ∈ 𝒜` for which either
(iv)′ `φ_A(t){1 − F(t)} ∈ L₁(0, ∞)` and is monotonic in `(0, ∞)`, or
(iv)″ `μ₁ < ∞` and either (iv)″_a `φ_A(t){1 − F(t)}` is of bounded variation in every finite
`t`-interval, or (iv)″_b `F ∈ 𝔖` (and `φ_A` is measurable),
`lim_{t→∞} P{x_t ∈ A | z} = (1/μ₁) ∫₀^∞ φ_A(v){1 − F(v)} dv` (3·4·2),
where the limit is zero if `μ₁ = ∞` (allowable under (iv)′).

Formalization Note.
* (iii) is built into `EquilibriumProcess` (`t₀` is real-valued, so `K_z` is a probability law).
* Hypothesis (iv) is about the one set `A` of the conclusion, and `μ₁ < ∞` belongs to (iv)″ only.
* "Monotonic" is non-decreasing or non-increasing on `(0, ∞)`; "bounded variation in every finite
  `t`-interval" is bounded variation on every `[0, b]` (the time axis is `t ≥ 0`); measurability of
  `φ_A` is part of `EquilibriumProcess`.
* The cases `μ₁ = ∞` (limit `0`) and `μ₁ < ∞` are stated separately; `1 − F(v)` is
  `F (Set.Ioi v)`. -/
theorem theorem_2 {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (hper : IsAperiodic E.F)
    (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (hiv :
      (IntegrableOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Ioi 0) ∧
        (MonotoneOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Ioi 0) ∨
          AntitoneOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Ioi 0))) ∨
      (mean E.F < ⊤ ∧
        ((∀ b : ℝ, BoundedVariationOn (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal)
            (Set.Icc 0 b)) ∨
          InClassS E.F))) :
    (mean E.F = ⊤ →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop (𝓝 0)) ∧
    (mean E.F ≠ ⊤ →
      Tendsto (fun t : ℝ => (E.P z {ω | E.x t ω ∈ A}).toReal) atTop
        (𝓝 ((mean E.F).toReal⁻¹ * ∫ v in Set.Ioi 0, E.φ A v * (E.F (Set.Ioi v)).toReal))) := by sorry

end SmithRegenerative.Equilibrium
