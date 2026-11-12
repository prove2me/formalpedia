-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_theorem_12
-- name    : PQNormIPM1352.Main.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:26.759796+00:00
-- url     : https://prove2.me/theorems/a2ec8ea3-c5be-4f81-978b-f4abda152421
-- title:
--   Theorem 12 — the inexact short-step IPM keeps $\lambda_{\eta}\le1/10$; $T\le\lceil 21\sqrt\nu\log(\eta_T/\eta_0)\rceil$
-- statement:
--   Let $F$ be a $\nu$-self-concordant barrier for $K \subseteq \mathbb R^N$ ($N \ge 1$) with invertible Hessian on $\mathrm{int}(K)$, let $c\in\mathbb R^N$, and let $x_0 \in \mathrm{int}(K)$ and $\eta_0 > 0$ satisfy $\lambda_{\eta_0}(x_0) \le 1/10$. Let $0 \le \delta \le 1/5$ and update
--   $$x^+ = x + \tilde\Delta_\eta(x),\qquad \eta^+ = \Big(1 + \frac1{20\sqrt\nu}\Big)\eta,$$
--   where $\tilde\Delta_\eta(x)$ is any approximate Newton step satisfying (3). Then:
--   1. every iterate stays in $\mathrm{int}(K)$, and $\lambda_{\eta^+}(x^+) \le 1/10$ at every step, so $\lambda_{\eta_t}(x_t) \le 1/10$ for all $t$ (the iterate $x_t$ is an approximate solution to $x^*_{\eta_t}$);
--   2. the number $T$ of iterations needed to reach $\eta_T = (1 + 1/(20\sqrt\nu))^T\eta_0$ satisfies
--   $$T \le \Big\lceil 21\sqrt\nu\,\log\frac{\eta_T}{\eta_0}\Big\rceil.$$
--
--   This is the invariant behind the iteration bound of Theorem 5.
--
--   Differences from the source:
--   - reading: K ⊆ ℝⁿ → N ≥ 1; reason: in ℝ⁰ every ν > 0 is a complexity parameter, and clause 2 fails for small ν (21√ν log(1+1/(20√ν)) < 1 at ν = 0.01); for N ≥ 1 with invertible Hessian ν ≥ 1 [NN94]
--   - reading: H(x)⁻¹ in the Newton step → hypothesis: the Hessian is positive definite on int(K); reason: the Newton step presupposes an invertible Hessian
--   - reading: “we reach an approximate solution to x*_{η_T}” → λ_{η_t}(x_t) ≤ 1/10 and x_t ∈ int(K) for every t; reason: the invariant the proof of Theorem 5 (p. 25) uses
--   - encoding: x₀ and η₀ with λ_{η₀}(x₀) ≤ 1/10 → η₀ > 0 and an infinite run with x 0 = x₀; reason: §2.2.2 takes η > 0 throughout; every finite run extends with exact Newton steps
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Theorem 12, printed p. 23 (PDF p. 24); proof p. 24

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_IPM

namespace PQNormIPM1352.Main

/-- **Theorem 12** (Pirazzini–Spielman, STOC 2027 #1352, p. 23). Let `F` be a `ν`-self-concordant
barrier for `K ⊆ ℝᴺ` (`N ≥ 1`) with invertible Hessian, `c ∈ ℝᴺ`, `x₀ ∈ int(K)` and `η₀ > 0` with
`λ_{η₀}(x₀) ≤ 1/10`, and `0 ≤ δ ≤ 1/5`. Along every run `x⁺ = x + Δ̃_η(x)`,
`η⁺ = (1 + 1/(20√ν)) η` with δ-approximate Newton steps (3), every iterate stays in `int(K)` and
satisfies `λ_{η_t}(x_t) ≤ 1/10`. In particular, the number `T` of iterations needed to reach
`η_T = (1 + 1/(20√ν))^T η₀` satisfies `T ≤ ⌈21 √ν log(η_T / η₀)⌉`. -/
theorem theorem_12 {N : ℕ} (hN : 0 < N) (K : Set (Vec N)) (F : Vec N → ℝ) (ν : ℝ)
    (hF : IsNuSCB K F ν) (hH : ∀ y ∈ interior K, (hessMat F y).PosDef) (c : Vec N)
    (x₀ : Vec N) (hx₀ : x₀ ∈ interior K) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hdec₀ : newtonDecrement (penalized F c η₀) x₀ ≤ 1 / 10) (δ : ℝ) (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ 1 / 5) :
    (∀ x : ℕ → Vec N, IsApproxPathRun F c ν δ η₀ x₀ x →
      ∀ t : ℕ, x t ∈ interior K ∧
        newtonDecrement (penalized F c (pathParam ν η₀ t)) (x t) ≤ 1 / 10) ∧
    ∀ T : ℕ, (T : ℤ) ≤ ⌈21 * Real.sqrt ν * Real.log (pathParam ν η₀ T / η₀)⌉ := by sorry

end PQNormIPM1352.Main
