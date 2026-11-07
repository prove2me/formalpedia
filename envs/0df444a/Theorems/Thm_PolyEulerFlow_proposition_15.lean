-- Prove2me | Theorems.Thm_PolyEulerFlow_proposition_15
-- name    : PolyEulerFlow.proposition_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:56.297545+00:00
-- url     : https://prove2.me/theorems/96a91e43-93b5-46e9-92d5-a746c4caae21
-- title:
--   Proposition 15 — logical traces under refinement and forcing
-- statement:
--   In the setting of Theorem 14 (the explicit compiled field and initialization, constants $B,r^*,c_-\le c_+,s_0$, a valid prefix $C_0,\dots,C_T$ with gain bound $\Gamma$ satisfying (6)):
--
--   1. Let $\lambda_h$ be an observation with values in a finite alphabet, constant on each closed $r_0h$-neighborhood (sup norm) of a valid configuration. For every allowed mesh and disturbance, the observations of $Y$ at the cycle sections are exactly $\lambda_h(C_0),\lambda_h(C_1),\dots,\lambda_h(C_T)$.
--   2. For a resetting halting run and every measurable forcing $\xi$ with $\|\xi(t)\|_\infty\le\nu$ almost everywhere, a continuous solution exists, and for every such solution $Z$: its continuous phase entries $\theta_0=0$, $\theta_{j+1}=\inf\{t\ge\theta_j:p_{j+1}(Z(t))\ge9/10\}$ exist, and its cycle sections $\theta_{4j}$, $0\le j\le T$, have the same observations, satisfy (7) and (8), and are the limits, as $\eta\to0^+$, of the corresponding sections of the constant-mesh-$\eta$ Euler executions whose disturbances are the cell averages of $\xi$. The exact flow is the case $\xi=0$.
--
--   Every property of the finite word of observations is therefore the same for all meshes, all disturbances and the forced flows.
--
--   Differences from the source:
--   - generalization: the field of Theorem 14 (existential) → the explicit compiled field of §6.3 and the intended initialization; reason: as in Theorem 14
--   - reading: (7) and (8) in the setting of Theorem 14 → constants B, r∗, c₋, c₊, s₀ existential in this statement, before s, the prefix, the mesh and the forcing, with (6) as hypothesis; reason: the proposition reuses Theorem 14's constants; quantified the same way
--   - reading: the continuous solution has ordered cycle-section times; after the initial section they occur at every fourth successive phase crossing of 9/10 → existence of a solution, then for every solution the sections are θ_{4j} of the strict-infimum phase entries, which exist; reason: Lemma 16 defines the section times this way; ordering follows from (8)
--   - reading: they are the limits of the corresponding Euler sections with constant mesh → convergence of η·(4j-th phase entry index) to θ_{4j} along η → 0⁺; reason: the limit over the whole family of meshes (Lemma 16)
--   - generalization: every allowed mesh (constant η in Theorem 14's display) → every admissible variable mesh; reason: Theorem 14 states its conclusions for both
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Proposition 15, pp.18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants
import Definitions.Def_PolyEulerFlow_IsForcedSolution

open Filter Topology

namespace PolyEulerFlow

/-- **Proposition 15 (Logical traces under refinement and forcing)**, pp.18–19 (PDF 20–21). Bournez, One Polynomial Field for Every Euler Step
and the Flow (manuscript, sha256 c4e01b2b…).

In the setting of Theorem 14, let `λ_h` be an observation with values in a finite alphabet, constant on each closed `r₀h`-neighborhood (sup norm) of a
valid configuration. Then the observations of `Y` at the cycle sections are exactly `λ_h(C₀), …, λ_h(C_T)` for every allowed mesh and disturbance. For a
resetting halting run and every measurable forcing `ξ` with `‖ξ(t)‖∞ ≤ ν` almost everywhere, the continuous solution exists, and its cycle sections
have the same observations, satisfy (7) and (8), occur after the initial section at every fourth successive crossing of the clock threshold `9/10`,
and are the limits of the corresponding constant-mesh Euler sections when the forcing is averaged on cells.

**Formalization Note** The field is the explicit compiled field of §6.3 and the initialization the intended initial section of p.27, as in Theorem 14;
the constants `B, r∗, c₋, c₊, s₀` play the roles they have in (6)–(8). The continuous sections are `θ_{4j}`, with `θ₀ = 0` and
`θ_{j+1} = inf{t ≥ θ_j : p_{j+1}(Z(t)) ≥ 9/10}`, all of whose defining sets are asserted nonempty. The limit is along `η → 0⁺`. The mesh of the
discrete clause is variable and contains every constant mesh. The exact flow is the case `ξ = 0`. -/
theorem proposition_15 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (B rstar cm cp : ℝ) (s0 : ℕ), 0 < B ∧ 0 < rstar ∧ 0 < cm ∧ cm ≤ cp ∧ 0 < s0 ∧
        ∀ s : ℕ, s0 ≤ s →
          let h := scale s
          let ε := h ^ K
          ∀ (ν : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) (Γ : ℝ), 0 ≤ ν → ν ≤ ε ^ 2 → 1 ≤ T →
            prog.IsValidPrefix h C T → prog.IsGainBound h C T Γ → B * Γ * T * deltaEps ε ν ≤ rstar * h →
            let f := compiledField prog K h
            let Z0 := initState prog K h (C 0)
            let IsObservation : ∀ {α : Type}, ((Fin m → ℝ) → α) → Prop := fun obs =>
              ∀ C' ∈ prog.valid h, ∀ Y : Fin m → ℝ, ‖Y - C'‖ ≤ prog.r0 * h → obs Y = obs C'
            (∀ (α : Type) [Finite α] (obs : (Fin m → ℝ) → α), IsObservation obs →
              ∀ (η : ℕ → ℝ) (ξ : ℕ → CompiledState m g), IsAdmissibleMesh η → IsPermittedDisturbance ν ξ →
                ∃ kk : ℕ → ℕ, IsPhaseEntriesUpTo phaseBit (eulerOrbit f Z0 η ξ) 0 (4 * T) kk ∧
                  ∀ j ≤ T, obs (dataY (eulerOrbit f Z0 η ξ (kk (4 * j)))) = obs (C j)) ∧
            (prog.IsResettingHaltRun h C T →
              ∀ ξ : ℝ → CompiledState m g, IsPermittedForcing ν ξ →
                (∃ z : ℝ → CompiledState m g, IsForcedSolution f Z0 ξ z) ∧
                ∀ z : ℝ → CompiledState m g, IsForcedSolution f Z0 ξ z →
                  let θ := contPhaseEntry phaseBit z
                  ContPhaseEntriesExist phaseBit z ∧
                  ∀ j ≤ T,
                    (∀ (α : Type) [Finite α] (obs : (Fin m → ℝ) → α), IsObservation obs →
                      obs (dataY (z (θ (4 * j)))) = obs (C j)) ∧
                    ‖dataY (z (θ (4 * j))) - C j‖ ≤ B * Γ * j * deltaEps ε ν ∧
                    (j < T → cm * (1 + s) ≤ θ (4 * j + 4) - θ (4 * j) ∧ θ (4 * j + 4) - θ (4 * j) ≤ cp * (1 + s)) ∧
                    Tendsto (cellEulerEntryTime phaseBit f Z0 ξ (4 * j)) (𝓝[>] 0) (𝓝 (θ (4 * j)))) := by sorry

end PolyEulerFlow
