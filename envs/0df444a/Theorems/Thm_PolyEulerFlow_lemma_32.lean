-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_32
-- name    : PolyEulerFlow.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:46.30359+00:00
-- url     : https://prove2.me/theorems/328f0342-0faa-4ae2-b47b-fd56c54e1f04
-- title:
--   Lemma 32 — cut separation
-- statement:
--   With the constants of Lemma 31, $L=\log(1/\varepsilon)$, $\vartheta=7/8$, $\Delta_\varepsilon=(1+L)(\varepsilon^{1/4}+\nu)$ (33) and $t^{cut}_j$ the first grid time at least $t_j+\vartheta L$, there are $C>0$ and $\varepsilon_1>0$ such that, for $0<\varepsilon\le\varepsilon_1$, $0\le\nu\le\varepsilon^2$, every mesh and every disturbance of level $\nu$, on every phase $I_j=[t_j,t_{j+1})$ of the exact or perturbed clock started at the entry conditions (29),
--   $$\int_{t_j}^{t^{cut}_j}|p_{j+1}|\,d\eta t\le C\Delta_\varepsilon,\qquad\int_{t^{cut}_j}^{t_{j+1}}|p_{j-1}|\,d\eta t\le C\Delta_\varepsilon,\tag{34}$$
--   $$\int_{t_j}^{t_{j+1}}|p_{j+2}|\,d\eta t\le C\Delta_\varepsilon,\qquad\int_{t_j}^{t_{j+1}}|p_{j-1}|\,d\eta t\le C,\tag{35}$$
--   and the active gate $p_j$ is at least $9/10$ on an interval of length at least $L-C$ starting at the entry of the phase. Here $\int_a^b f\,d\eta t=\sum_{a\le t_k<b}\eta_kf(t_k)$.
--
--   The cut separates the comparison, loading and copy operations of a cycle: before it the next gate has negligible mass, after it the previous gate has negligible mass.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - reading: on every phase of the exact or perturbed clock → the clock orbit started from the clock box at the entry conditions (29) of Lemma 31, whose constants are existential jointly with C; reason: the phases of the clock are exactly these orbits (Lemma 31)
--   - reading: the active gate is at least 9/10 on an interval of length at least L − C, starting at the entry → p_j ≥ 9/10 at every grid time t_k ≤ L − C (with t_j = 0); reason: the interval is [t_j, t_j + L − C]
--   - encoding: the integrals ∫ dηt → grid sums Σ_{a ≤ k < b} η_k f(z_k) between grid indices; reason: this is their definition on p.27
--   - encoding: a phase starting at t_j → a clock orbit started at index 0 with the shifted mesh and disturbances; reason: the scheme is autonomous
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 32, p.30 (PDF 32), with ϑ, t^cut_j and (33) on p.30

import Mathlib
import Definitions.Def_PolyEulerFlow_IsUniformClock

namespace PolyEulerFlow

/-- **Lemma 32 (Cut separation)**, p.30 (PDF 32). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

With the constants of Lemma 31, `L = log(1/ε)`, `ϑ = 7/8`, `∆ε = (1 + L)(ε^{1/4} + ν)` (33), and `t^cut_j` the first grid time at least
`t_j + ϑL`: on every phase `I_j = [t_j, t_{j+1})` of the exact or perturbed clock,
`∫_{t_j}^{t^cut_j} |p_{j+1}| dηt ≤ C∆ε`, `∫_{t^cut_j}^{t_{j+1}} |p_{j-1}| dηt ≤ C∆ε` (34),
`∫_{t_j}^{t_{j+1}} |p_{j+2}| dηt ≤ C∆ε`, `∫_{t_j}^{t_{j+1}} |p_{j-1}| dηt ≤ C` (35),
and the active gate is at least `9/10` on an interval of length at least `L - C` starting at the entry of the phase.

**Formalization Note** The integrals are the grid sums of p.27, `Σ_{a ≤ t_k < b} η_k f(t_k)`. A phase is the clock orbit started, at index `0`,
from a state of the clock box satisfying the entry conditions (29) of Lemma 31; the conclusion is attached to the constants of Lemma 31,
whose existence is part of the statement. The mesh is variable (Corollary 39, p.34). -/
theorem lemma_32 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∃ C ε1 : ℝ, 0 < C ∧ 0 < ε1 ∧
      ∀ ε ν : ℝ, 0 < ε → ε ≤ ε1 → 0 ≤ ν → ν ≤ ε ^ 2 →
      ∀ (η : ℕ → ℝ) (ξ : ℕ → ClockState) (X0 : ClockState) (j : Fin 4),
        IsAdmissibleMesh η → IsPermittedDisturbance ν ξ → clockBox ε ν X0 → clockEntry A0 B0 ε j X0 →
        let z := eulerOrbit (clockField ε) X0 η ξ
        let L := Real.log (1 / ε)
        let kcut := firstGrid η ((7 / 8) * L)
        let p : Fin 4 → ℕ → ℝ := fun i k => z k (.inl i)
        ∃ k1 : ℕ, IsFirstAfter (AboveThreshold clockBit (j + 1)) z 0 k1 ∧
          gridSum η (fun k => |p (j + 1) k|) 0 kcut ≤ C * deltaEps ε ν ∧
          gridSum η (fun k => |p (j - 1) k|) kcut k1 ≤ C * deltaEps ε ν ∧
          gridSum η (fun k => |p (j + 2) k|) 0 k1 ≤ C * deltaEps ε ν ∧
          gridSum η (fun k => |p (j - 1) k|) 0 k1 ≤ C ∧
          ∀ k, physTime η k ≤ L - C → 9 / 10 ≤ p j k := by sorry

end PolyEulerFlow
