-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_theorem_5
-- name    : PQNormIPM1352.Main.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:27.121748+00:00
-- url     : https://prove2.me/theorems/e8b75f0f-af2a-43e2-aec1-68a97737cc88
-- title:
--   Theorem 5 — $\lceil C\sqrt\nu\log\frac{\nu}{\varepsilon\eta_0}\rceil$ inexact Newton steps give gap $\le\varepsilon$; $C=22$ if $\nu\ge40$ (corrected: general $C$ needs $\nu\ge2\varepsilon\eta_0$)
-- statement:
--   Let $F$ be a $\nu$-self-concordant barrier for $K\subseteq\mathbb R^N$ with invertible Hessian on $\mathrm{int}(K)$, let $c\in\mathbb R^N$, and let $x^*\in K$ minimize $\langle c,\cdot\rangle$ over $K$. Let $x_0\in\mathrm{int}(K)$ and $0<\eta_0<1$ satisfy $\lambda_{\eta_0}(x_0)\le 1/10$, let $0<\varepsilon<1$ and $0<\delta<1/5$, and run the method of Theorem 12, each iteration involving a $\delta$-approximate Newton step (3).
--   1. There is a universal constant $C > 1$ such that, whenever $\nu/(\varepsilon\eta_0) \ge 2$, after
--   $$T = \Big\lceil C\sqrt\nu\,\log\frac{\nu}{\varepsilon\eta_0}\Big\rceil$$
--   iterations the point $x_T$ lies in $\mathrm{int}(K)$ and $\langle c, x_T\rangle - \langle c, x^*\rangle \le \varepsilon$.
--   2. If $\nu \ge 40$, the same holds with $C = 22$.
--
--   Theorem 5 is the iteration bound used for Algorithm 1 with $\nu = 3s+2$.
--
--   **Formalization Note** $C$ is quantified before all data ($N$, $K$, $F$, $\nu$, $c$, $x_0$, $\eta_0$, $\varepsilon$, $\delta$). The second clause carries no ratio condition: $\nu\ge40$, $\varepsilon<1$ and $\eta_0<1$ give $\nu/(\varepsilon\eta_0) > 40$.
--
--   Differences from the source:
--   - correction: there exists a constant C > 1 such that ⌈C√ν log(ν/(εη₀))⌉ iterations suffice, for every ν, ε, η₀ → the universal-C clause under the extra hypothesis ν/(εη₀) ≥ 2 (the C = 22 clause for ν ≥ 40 is unchanged); reason: false for every C as ν/(εη₀) → 1: K = [0,∞), F = −log x (ν = 1), c = 1, x* = 0, x₀ = 1.1/η₀ (λ = 0.1), δ = 0.19 and Δ̃ = 0.81Δ give x₁ = 1.0109/η₀ > 1 > ε, while T = ⌈C log(1/(εη₀))⌉ = 1 once εη₀ > e^{−1/C}
--   - reading: H(x)⁻¹ in the Newton step → hypothesis: the Hessian is positive definite on int(K); reason: the Newton step presupposes an invertible Hessian
--   - encoding: “after T iterations we reach a point x” → the T-th iterate x_T of every infinite run; reason: every finite run extends with exact Newton steps; the gap at x_T is the claim
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Theorem 5, printed p. 6 (PDF p. 7); proof p. 25

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_IPM

open scoped RealInnerProductSpace

namespace PQNormIPM1352.Main

/-- **Theorem 5** (Pirazzini–Spielman, STOC 2027 #1352, p. 6; corrected). Let `F` be a
`ν`-self-concordant barrier for `K` with invertible Hessian, `c ∈ ℝᴺ`, `x*` a minimizer of
`⟨c, ·⟩` over `K`, `x₀ ∈ int(K)` and `0 < η₀ < 1` with `λ_{η₀}(x₀) ≤ 1/10`, `0 < ε < 1`,
`0 < δ < 1/5`. Run the method of Theorem 12 with δ-approximate Newton steps (3).
1. There is a universal constant `C > 1` such that, whenever `ν / (ε η₀) ≥ 2`, after
   `T = ⌈C √ν log(ν / (ε η₀))⌉` iterations the point `x_T` lies in `int(K)` and
   `⟨c, x_T⟩ − ⟨c, x*⟩ ≤ ε`.
2. If `ν ≥ 40`, the same holds with `C = 22` (no further condition). -/
theorem theorem_5 :
    (∃ C : ℝ, 1 < C ∧
      ∀ {N : ℕ} (K : Set (Vec N)) (F : Vec N → ℝ) (ν : ℝ), IsNuSCB K F ν →
        (∀ y ∈ interior K, (hessMat F y).PosDef) →
        ∀ (c xstar : Vec N), xstar ∈ K → (∀ y ∈ K, ⟪c, xstar⟫ ≤ ⟪c, y⟫) →
        ∀ (x₀ : Vec N), x₀ ∈ interior K → ∀ η₀ : ℝ, 0 < η₀ → η₀ < 1 →
        newtonDecrement (penalized F c η₀) x₀ ≤ 1 / 10 →
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 / 5 → 2 ≤ ν / (ε * η₀) →
        ∀ x : ℕ → Vec N, IsApproxPathRun F c ν δ η₀ x₀ x →
          x ⌈C * Real.sqrt ν * Real.log (ν / (ε * η₀))⌉₊ ∈ interior K ∧
          ⟪c, x ⌈C * Real.sqrt ν * Real.log (ν / (ε * η₀))⌉₊⟫ - ⟪c, xstar⟫ ≤ ε) ∧
    (∀ {N : ℕ} (K : Set (Vec N)) (F : Vec N → ℝ) (ν : ℝ), IsNuSCB K F ν → 40 ≤ ν →
        (∀ y ∈ interior K, (hessMat F y).PosDef) →
        ∀ (c xstar : Vec N), xstar ∈ K → (∀ y ∈ K, ⟪c, xstar⟫ ≤ ⟪c, y⟫) →
        ∀ (x₀ : Vec N), x₀ ∈ interior K → ∀ η₀ : ℝ, 0 < η₀ → η₀ < 1 →
        newtonDecrement (penalized F c η₀) x₀ ≤ 1 / 10 →
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 / 5 →
        ∀ x : ℕ → Vec N, IsApproxPathRun F c ν δ η₀ x₀ x →
          x ⌈22 * Real.sqrt ν * Real.log (ν / (ε * η₀))⌉₊ ∈ interior K ∧
          ⟪c, x ⌈22 * Real.sqrt ν * Real.log (ν / (ε * η₀))⌉₊⟫ - ⟪c, xstar⟫ ≤ ε) := by sorry

end PQNormIPM1352.Main
