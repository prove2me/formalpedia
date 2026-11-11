-- Prove2me | Theorems.Thm_SpaceReset_Hardness_theorem_7
-- name    : SpaceReset.Hardness.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:10.375285+00:00
-- url     : https://prove2.me/theorems/7ac481bc-f4c9-4f33-b6b8-a0d4cd6267f0
-- title:
--   Theorem 7 — two endpoints with different decoded labels
-- statement:
--   Let $E_0,E_1,Y$ be finite-dimensional, $d_i=\dim E_i$. Let $\xi_x\ge0$ ($x\in[A]$) act on $E_0$ with $\sum_x\operatorname{Tr}\xi_x=1$, and let $V:E_0\to Y\otimes E_1$ be an isometry. Let $f:[A]\to[B]$ have exactly $A/B$ preimages of every element, and let $\{E_x\}_{x\in[A]}$, $\{F_z\}_{z\in[B]}$ be POVMs on $E_0$, $E_1$. Put
--   $$e_0=1-\sum_x\operatorname{Tr}(E_x\xi_x),\qquad e_1=1-\sum_x\operatorname{Tr}\big((I_Y\otimes F_{f(x)})V\xi_xV^\dagger\big).$$
--   Let $\rho_x$ be states on $Y$ with $\|\rho_x\|_\infty\le1/M$, and
--   $$\Omega_{XY}=\sum_x|x\rangle\langle x|\otimes\operatorname{Tr}_{E_1}(V\xi_xV^\dagger),\quad \tau_{XY}=\frac1A\sum_x|x\rangle\langle x|\otimes\rho_x,\quad \delta=\tfrac12\|\Omega-\tau\|_1.$$
--   Then
--   $$\sqrt{d_0d_1}\ \ge\ \sqrt{ABM}\,\Big[1-\tfrac32\delta-\sqrt{e_0}-\sqrt{e_1}\Big]_+ .$$
--
--   No relation between $E_x$ and $F_{f(x)}$ and no rank or spectral assumption on the initializer is required. This robust two-time dimension bound is the converse engine of the space–discard frontier.
--
--   Differences from the source:
--   - encoding: ‖ρ_x‖_∞ ≤ 1/M → ρ_x ≤ (1/M)·I in the Loewner order, with 0 < M; reason: for positive semidefinite ρ_x the two are equivalent; 1/M presupposes M > 0
--   - encoding: f has exactly C = A/B preimages of every element → every fibre of f has size c with c·B = A; reason: same condition, stated without natural division
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), Theorem 7, §2.3, pp. 13–14 (eq. (6))

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_SpaceReset_Hardness_Quantum

set_option autoImplicit false

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

namespace SpaceReset.Hardness

/-- Theorem 7 (Two endpoints with different decoded labels), §2.3, pp. 13–14, eq. (6). -/
theorem theorem_7 {E₀ E₁ Y : Type} [Fintype E₀] [DecidableEq E₀] [Fintype E₁] [DecidableEq E₁]
    [Fintype Y] [DecidableEq Y] (A B : ℕ) (M : ℝ) (hM : 0 < M)
    (ξ : Fin A → Matrix E₀ E₀ ℂ) (hξ : ∀ x, (ξ x).PosSemidef) (hξ1 : ∑ x, (ξ x).trace = 1)
    (V : Matrix (Y × E₁) E₀ ℂ) (hV : Vᴴ * V = 1)
    (f : Fin A → Fin B) (hf : ∀ z : Fin B, (Finset.univ.filter (fun x => f x = z)).card * B = A)
    (Ex : Fin A → Matrix E₀ E₀ ℂ) (hEx : IsPOVM Ex)
    (Fz : Fin B → Matrix E₁ E₁ ℂ) (hFz : IsPOVM Fz)
    (ρ : Fin A → Matrix Y Y ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hρM : ∀ x, ρ x ≤ ((1 / M : ℝ) : ℂ) • (1 : Matrix Y Y ℂ)) :
    let e₀ : ℝ := 1 - (∑ x, (Ex x * ξ x).trace).re
    let e₁ : ℝ := 1 - (∑ x, (((1 : Matrix Y Y ℂ) ⊗ₖ Fz (f x)) * (V * ξ x * Vᴴ)).trace).re
    let Ω : Matrix (Fin A × Y) (Fin A × Y) ℂ :=
      fun p p' => if p.1 = p'.1 then ptraceRight (V * ξ p.1 * Vᴴ) p.2 p'.2 else 0
    let τ : Matrix (Fin A × Y) (Fin A × Y) ℂ :=
      fun p p' => if p.1 = p'.1 then ((1 : ℂ) / (A : ℂ)) * ρ p.1 p.2 p'.2 else 0
    let δ : ℝ := WildeQIT.traceNorm (Ω - τ) / 2
    Real.sqrt (Fintype.card E₀ * Fintype.card E₁) ≥
      Real.sqrt (A * B * M) * max 0 (1 - (3 / 2) * δ - Real.sqrt e₀ - Real.sqrt e₁) := by sorry

end SpaceReset.Hardness
