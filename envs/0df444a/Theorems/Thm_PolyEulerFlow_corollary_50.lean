-- Prove2me | Theorems.Thm_PolyEulerFlow_corollary_50
-- name    : PolyEulerFlow.corollary_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:29.765048+00:00
-- url     : https://prove2.me/theorems/690a0417-1b34-4324-a0c3-f305e1a240e8
-- title:
--   Corollary 50 — continuous bounded-forcing semantics
-- statement:
--   For the constructed robust field (the compiled field of §6.3 run on a valid prefix $C_0,\dots,C_T$, $T\ge1$, ending with a resetting halt, with (6) at $\nu=h^{2K}$), let $\xi:[0,\infty)\to\mathbb R^m$ be any measurable forcing with $\|\xi(t)\|_\infty\le h^{2K}$ almost everywhere. The absolutely continuous solution of
--   $$\dot z(t)=F(h,z(t))+\xi(t),\qquad z(0)=c(h,C_0),$$
--   exists globally; every such solution stays in the same compact active box, and has the same stable decision after the stated physical horizon: its data stay within $O(\Delta_\varepsilon)$ of the halting configuration $C_T$ at every time $t\ge c_+(1+s)T$.
--
--   Differences from the source:
--   - reading: the constructed robust field → the explicit compiled field and initialization of a separated affine program, on a resetting halting valid prefix satisfying (6) with ν = h^{2K}, K ≥ 256; reason: Theorem 14 with ν = h^{2K}, the case used by Theorem 1
--   - reading: the same stable decision after the stated physical horizon → ‖Y(t) − C_T‖∞ ≤ C_halt∆ε for every t ≥ c₊(1+s)T; reason: as in Theorem 14's flow clause
--   - reading: the absolutely continuous solution exists globally → a continuous solution of the integral equation on [0, ∞) exists, and the bounds hold for every such solution; reason: absolutely continuous solutions are the solutions of the integral equation
--   - reading: the same compact active box → a box [lo, hi] existential with the other constants, before s and the forcing; reason: the box is fixed by the construction
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Corollary 50, pp.37–38 (PDF 39–40)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants
import Definitions.Def_PolyEulerFlow_IsForcedSolution

namespace PolyEulerFlow

/-- **Corollary 50 (Continuous bounded-forcing semantics)**, pp.37–38 (PDF 39–40). Bournez, One Polynomial Field for Every Euler Step and the
Flow (manuscript, sha256 c4e01b2b…).

For the constructed robust field (the compiled field of a resetting halting run, Theorem 14 with `ν = h^{2K}`), let `ξ : [0, ∞) → ℝ^m` be any
measurable forcing with `‖ξ(t)‖∞ ≤ h^{2K}` almost everywhere. The absolutely continuous solution of `ż = F(h, z) + ξ(t)`, `z(0) = c(h, C₀)` exists
globally, stays in the same compact active box, and has the same stable decision after the stated physical horizon.

**Formalization Note** The construction is that of Theorem 14: the explicit compiled field, the intended initialization, a valid prefix
`C₀, …, C_T` (`T ≥ 1`) with gain bound `Γ` satisfying (6) at `ν = h^{2K}`, ending with a resetting halt. "The same stable decision after the stated
horizon" is read as for Theorem 14: the data stay within `O(∆ε)` of the halting configuration `C_T` at every time `t ≥ c₊(1+s)T`. Every solution
satisfies the bounds, and one exists. -/
theorem corollary_50 :
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (lo hi : CompiledState m g) (B rstar cp Chalt : ℝ) (s0 : ℕ),
        lo ≤ hi ∧ 0 < B ∧ 0 < rstar ∧ 0 < cp ∧ 0 < Chalt ∧ 0 < s0 ∧
        ∀ s : ℕ, s0 ≤ s →
          let h := scale s
          let ε := h ^ K
          let ν := h ^ (2 * K)
          ∀ (C : ℕ → Fin m → ℝ) (T : ℕ) (Γ : ℝ), 1 ≤ T →
            prog.IsValidPrefix h C T → prog.IsGainBound h C T Γ → B * Γ * T * deltaEps ε ν ≤ rstar * h →
            prog.IsResettingHaltRun h C T →
            let f := compiledField prog K h
            let Z0 := initState prog K h (C 0)
            ∀ ξ : ℝ → CompiledState m g, IsPermittedForcing ν ξ →
              (∃ z : ℝ → CompiledState m g, IsForcedSolution f Z0 ξ z) ∧
              ∀ z : ℝ → CompiledState m g, IsForcedSolution f Z0 ξ z →
                (∀ τ : ℝ, 0 ≤ τ → z τ ∈ Set.Icc lo hi) ∧
                ∀ τ : ℝ, cp * (1 + s) * T ≤ τ → ‖dataY (z τ) - C T‖ ≤ Chalt * deltaEps ε ν := by sorry

end PolyEulerFlow
