-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_tail_limit_3_4_7
-- name    : SmithRegenerative.Equilibrium.tail_limit_3_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:47.384765+00:00
-- url     : https://prove2.me/theorems/764a1781-cfa7-4b17-99f0-43dfa2da221d
-- title:
--   (3·4·7) — tail limit ∫₀^{t−Δ}{1 − F(t − v)} dH(v) → (1/μ₁)∫_Δ^∞{1 − F(v)}dv ≤ ε for large Δ
-- statement:
--   Let $E$ be an aperiodic equilibrium process with cycle law $F$ of finite mean $\mu_1$. Fix a boundary condition $z$, and let $H = H_{K_z}$ be its renewal measure. Then for every $\Delta > 0$
--   $$
--   \lim_{t\to\infty} \int_0^{t-\Delta} \{1 - F(t-v)\}\, dH(v) = \frac{1}{\mu_1} \int_\Delta^\infty \{1 - F(v)\}\, dv.
--   $$
--
--   For every $\varepsilon>0$, the right-hand side is at most $\varepsilon$ for all sufficiently large $\Delta$. In the proof of Theorem 2 this bounds the contribution of regenerations that occurred more than $\Delta$ before time $t$.
--
--   **Formalization Note** The limit identity and the page's small-tail clause are both stated. $1 - F(v) = F((v,\infty))$ and the integral is over $[0, t-\Delta]$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §3·4, proof of Theorem 2, (3·4·7), p. 16

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

namespace SmithRegenerative.Equilibrium

open MeasureTheory Filter Topology

/-- **The tail limit (3·4·7)** (Smith 1955, §3·4, proof of Theorem 2, p. 16; unnumbered result).
Let `E` be an aperiodic equilibrium process with `μ₁ < ∞` and let `z` be a boundary condition,
with renewal measure `H = H_{K_z}`. Then for every `Δ > 0`
`lim_{t→∞} ∫₀^{t−Δ} {1 − F(t − v)} dH(v) = (1/μ₁) ∫_Δ^∞ {1 − F(v)} dv`,
and this common value is at most `ε` when `Δ` is chosen sufficiently large.

Formalization Note: `1 − F(v)` is `F (Set.Ioi v)`; the integral is over `[0, t − Δ]`.
The final quantifier states the page's choice of a sufficiently large `Δ` for every `ε > 0`. -/
theorem tail_limit_3_4_7 {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (z : Z)
    (hper : IsAperiodic E.F) (hμ : mean E.F < ⊤) :
    (∀ Δ : ℝ, 0 < Δ →
      Tendsto (fun t : ℝ => ∫ v in Set.Icc 0 (t - Δ), (E.F (Set.Ioi (t - v))).toReal
          ∂(renewalMeasure (E.K z) E.F)) atTop
        (𝓝 ((mean E.F).toReal⁻¹ * ∫ v in Set.Ioi Δ, (E.F (Set.Ioi v)).toReal))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      (mean E.F).toReal⁻¹ * ∫ v in Set.Ioi Δ, (E.F (Set.Ioi v)).toReal ≤ ε) := by sorry

end SmithRegenerative.Equilibrium
