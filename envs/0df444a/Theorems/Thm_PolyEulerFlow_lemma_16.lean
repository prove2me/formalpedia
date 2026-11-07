-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_16
-- name    : PolyEulerFlow.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:50.696915+00:00
-- url     : https://prove2.me/theorems/683c7edc-cf58-496f-ab08-c010f581c9e0
-- title:
--   Lemma 16 — intrinsic continuous sections
-- statement:
--   In the setting of Proposition 15 (a resetting halting run of the compiled field satisfying (6)), fix a measurable forcing $\xi$ with $\|\xi(t)\|_\infty\le\nu$ almost everywhere; a continuous solution $Z$ exists, and for every such solution put $\theta_0=0$ and, with indices modulo four,
--   $$\theta_{j+1}=\inf\{t\ge\theta_j:\ p_{j+1}(Z(t))\ge9/10\}.$$
--   For each constant mesh $\eta$, take as disturbance on a cell the average of $\xi$ on the cell, and let $t^{(\eta)}_j$ be the Euler phase entries. Then all $\theta_j$ are defined by nonempty sets, and for each fixed $j$,
--   $$t^{(\eta)}_{j+1}\to\theta_{j+1}\quad(\eta\to0^+),\qquad L-C_{dur}\le\theta_{j+1}-\theta_j\le4L+C_{dur}+D_{clk},$$
--   with $L=\log(1/\varepsilon)$ and the constants of Lemma 31. In particular the section times have no finite accumulation point and are defined from $Z$ alone.
--
--   Differences from the source:
--   - reading: for each fixed phase index j, t^{(η)}_{j+1} converges to θ_{j+1} as η → 0, for the whole family of meshes → Tendsto along the filter η → 0⁺ for every j; reason: the filter limit is over all small η, not a subsequence
--   - reading: let Z be the continuous solution → existence of a solution is asserted, and the conclusions hold for every solution; reason: Proposition 15 asserts the solution; uniqueness is not needed
--   - reading: the setting of Proposition 15; the constants of Lemma 31 → constants B, r∗, s₀ of (6) existential, and Lemma 31's constants existential jointly with the clock property; reason: as in Proposition 15 and Lemma 31
--   - generalization: the explicit compiled field (Theorem 14's construction) → the explicit compiled field of §6.3 and the intended initialization; reason: as in Theorem 14
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 16, p.19 (PDF 21)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants
import Definitions.Def_PolyEulerFlow_IsForcedSolution

open Filter Topology

namespace PolyEulerFlow

/-- **Lemma 16 (Intrinsic continuous sections)**, p.19 (PDF 21). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

In the setting of Proposition 15 (a resetting halting run of the compiled field), fix a measurable forcing `ξ` with `‖ξ‖∞ ≤ ν` and let `Z` be the
continuous solution. Put `θ₀ = 0` and `θ_{j+1} = inf{t ≥ θ_j : p_{j+1}(Z(t)) ≥ 9/10}` (indices modulo four). For each constant mesh `η`, with the cell
averages of `ξ` as disturbances, let `t^{(η)}_j` be the Euler phase entries. Then for each fixed phase index `j`, `t^{(η)}_{j+1} → θ_{j+1}` as `η → 0`,
for the whole family of meshes, and `L - C_dur ≤ θ_{j+1} - θ_j ≤ 4L + C_dur + D_clk` with `L = log(1/ε)` and the constants of Lemma 31.

**Formalization Note** The limit is along the filter `η → 0⁺`, not along a sequence. The existence of a solution is asserted with the statement (it is
part of Proposition 15). The defining sets of all `θ_j` are asserted nonempty. The constants `B, r∗, s₀` are those of the setting (6). -/
theorem lemma_16 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (B rstar : ℝ) (s0 : ℕ), 0 < B ∧ 0 < rstar ∧ 0 < s0 ∧
        ∀ s : ℕ, s0 ≤ s →
          let h := scale s
          let ε := h ^ K
          ∀ (ν : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) (Γ : ℝ), 0 ≤ ν → ν ≤ ε ^ 2 → 1 ≤ T →
            prog.IsValidPrefix h C T → prog.IsGainBound h C T Γ → B * Γ * T * deltaEps ε ν ≤ rstar * h →
            prog.IsResettingHaltRun h C T →
            let f := compiledField prog K h
            let Z0 := initState prog K h (C 0)
            ∀ ξ : ℝ → CompiledState m g, IsPermittedForcing ν ξ →
              (∃ z : ℝ → CompiledState m g, IsForcedSolution f Z0 ξ z) ∧
              ∀ z : ℝ → CompiledState m g, IsForcedSolution f Z0 ξ z →
                let θ := contPhaseEntry phaseBit z
                let L := Real.log (1 / ε)
                ContPhaseEntriesExist phaseBit z ∧
                ∀ j : ℕ, Tendsto (cellEulerEntryTime phaseBit f Z0 ξ (j + 1)) (𝓝[>] 0) (𝓝 (θ (j + 1))) ∧
                  L - Cdur ≤ θ (j + 1) - θ j ∧ θ (j + 1) - θ j ≤ 4 * L + Cdur + Dclk := by sorry

end PolyEulerFlow
