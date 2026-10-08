-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_decomposition_3_4_3
-- name    : SmithRegenerative.Equilibrium.decomposition_3_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:26.037859+00:00
-- url     : https://prove2.me/theorems/3f74c9af-a414-48bc-8f41-4b2228aaff18
-- title:
--   (3·4·3) — P{x_t ∈ A | z} = P{x_t ∈ A, t₀ > t | z} + ∫₀^t φ_A(t − τ){1 − F(t − τ)} dH_{K_z}(τ)
-- statement:
--   Let $x_t$ be an equilibrium process $\mathcal E(\mathfrak z, \mathcal A, \{t_i\})$ with cycle law $F$, delay laws $K_z$ and representing functions $\varphi_A$. Then for every boundary condition $z$, every $A \in \mathcal A$ and every $t \ge 0$,
--   $$
--   P\{x_t \in A \mid z\} = P\{x_t \in A,\ t_0 > t \mid z\} + \int_0^t \varphi_A(t-\tau)\{1 - F(t-\tau)\}\, dH_{K_z}(\tau).
--   $$
--
--   The identity splits the state probability according to whether a regeneration has occurred by time $t$: if it has, the epoch of the last one before $t$ has law $\{1 - F(t-\tau)\}\, dH_{K_z}(\tau)$ on $[0,t]$. It is the renewal-type equation from which Theorem 2 follows by the key renewal theorems.
--
--   **Formalization Note** $1 - F(v) = F((v,\infty))$, $H_{K_z}$ is the renewal measure of the delay law $K_z$, and the integral is over the closed interval $[0,t]$. The paper derives the identity with the symbol $T_{n_t}$ for the last regeneration epoch; see the definition of equilibrium process.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §3·4, proof of Theorem 2, (3·4·3), p. 15

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

namespace SmithRegenerative.Equilibrium

open MeasureTheory

/-- **The decomposition (3·4·3)** (Smith 1955, §3·4, proof of Theorem 2, p. 15; unnumbered result).
For an equilibrium process `𝓔(𝔷, 𝒜, {tᵢ})`, every boundary condition `z`, every `A ∈ 𝒜` and every
`t ≥ 0`,
`P{x_t ∈ A | z} = P{x_t ∈ A, t₀ > t | z} + ∫₀^t φ_A(t − τ){1 − F(t − τ)} dH_{K_z}(τ)`.

Formalization Note: `1 − F(v)` is `F (Set.Ioi v)`; `H_{K_z}` is `renewalMeasure (K z) F`; the
Stieltjes integral is over the closed interval `[0, t]`. No hypothesis beyond the equilibrium
property (and the certainty of `𝓔`, built into `EquilibriumProcess`) is used. -/
theorem decomposition_3_4_3 {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜) (t : ℝ) (ht : 0 ≤ t) :
    (E.P z {ω | E.x t ω ∈ A}).toReal =
      (E.P z {ω | E.x t ω ∈ A ∧ t < E.t 0 ω}).toReal +
        ∫ τ in Set.Icc 0 t, E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
          ∂(renewalMeasure (E.K z) E.F) := by sorry

end SmithRegenerative.Equilibrium
