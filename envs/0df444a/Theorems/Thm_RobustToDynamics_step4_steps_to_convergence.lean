-- Prove2me | Theorems.Thm_RobustToDynamics_step4_steps_to_convergence
-- name    : RobustToDynamics.step4_steps_to_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:58.602145+00:00
-- url     : https://prove2.me/theorems/0132a26a-d8e4-4ea3-84d1-f686d4be4ba8
-- title:
--   Step 4 — $\mathcal S=\mathcal S_r=\mathcal S_{\bar r}$ with $r=\lceil(\alpha_2/\alpha_1-1)/(1-\gamma)\rceil$, $\bar r=\lceil\log(\alpha_2/\alpha_1)/\log(1/\gamma)\rceil\le r$
-- statement:
--   Let $G\in\mathbb R^{n\times n}$ with $\rho(G)<1$, let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ with the origin in the interior of $P=\{x: Ax\le b\}$, let $M$ solve $G^TMG-M=-I$ (2.14), and let $l,u\in\mathbb R^n$ with $P\subseteq\{x: l\le x\le u\}$. With $\alpha_1$ from (2.15), $\alpha_2$ from (2.16) and $\gamma$ from (2.17), put
--   $$
--   \bar r=\left\lceil\frac{\log(\alpha_2/\alpha_1)}{\log(1/\gamma)}\right\rceil,\qquad r=\left\lceil\frac{(\alpha_2/\alpha_1)-1}{1-\gamma}\right\rceil .
--   $$
--   Then $\bar r\le r$ and
--   $$
--   \mathcal S=\mathcal S_r=\mathcal S_{\bar r}.
--   $$
--
--   This is the finite-convergence half of the first claim of Theorem 2.7 with an explicit step count.
--
--   **Formalization Note** Both ceilings are taken in $\mathbb N$ (a negative argument gives $0$). When $\gamma=0$, $\log(1/\gamma)$ evaluates to $0$ in Lean and $\bar r=0$, which matches the paper's $\log(1/\gamma)=+\infty$ (and indeed then $G=0$).
--
--   Differences from the source:
--   - generalization: l_i, u_i the minimum and maximum of x_i over P (P bounded) → any l, u with P ⊆ [l, u] (which forces P bounded, so no separate boundedness hypothesis); reason: the paper's coordinatewise LP bounds are one such box
--   - encoding: r = ⌈·⌉, a nonnegative integer → Nat.ceil (a negative argument gives 0); reason: S_r is defined for integers r ≥ 0, and S = S_0 = P whenever the ratio makes the ceiling nonpositive
--   - encoding: log(1/γ) with γ ∈ [0, 1); at γ = 0 it is +∞ and r̄ = 0 → Real.log (1 / 0) = 0, so r̄ = ⌈·/0⌉₊ = 0; reason: both give r̄ = 0
--   - encoding: M the unique solution of (2.14) → any M with GᵀMG − M = −I; reason: by uniqueness (Step 1) this is the same matrix
--   - generalization: rational data → real data; reason: the statement for real matrices specializes to rational ones by casting
--   - encoding: ρ(G) = max of |λ| over the (real or complex) eigenvalues → specRadius, the supremum of |z| over the complex spectrum; reason: the complex spectrum of an n × n matrix is finite and nonempty for n ≥ 1, so the supremum is the maximum; same value
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 4, p.16

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_feasibleSet
import Definitions.Def_RobustToDynamics_outerApprox
import Definitions.Def_RobustToDynamics_alpha1
import Definitions.Def_RobustToDynamics_alpha2
import Definitions.Def_RobustToDynamics_gamma

open Matrix

namespace RobustToDynamics

/-- **Step 4: `S = S_r = S_r̄` for the explicit step counts.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 4, p.16: "r̄ = ⌈log(α1/α2) / log γ⌉ = ⌈log(α2/α1) / log(1/γ)⌉ ≤ ⌈((α2/α1) − 1) / (1 − γ)⌉ =: r
… This establishes that S = Sr (in fact, we have shown that S = Sr = Sr̄)."

Let `ρ(G) < 1`, let the origin lie in the interior of `P = {x | Ax ≤ b}`, let `M` solve
`GᵀMG − M = −I` (2.14), and let `P ⊆ {x | l ≤ x ≤ u}`. With `α₁` from (2.15), `α₂` from (2.16) and
`γ` from (2.17), put `r = ⌈(α₂/α₁ − 1)/(1 − γ)⌉` and `r̄ = ⌈log(α₂/α₁)/log(1/γ)⌉` (rounded up to a
nonnegative integer). Then `r̄ ≤ r` and `S = S_r = S_r̄`.

**Formalization Note.** `⌈·⌉₊` is `Nat.ceil` (negative values give `0`). `ρ(G)` is `specRadius`.
`l, u` are any box bounds with `P ⊆ [l, u]` (a generalization of the paper's coordinatewise LP
minima and maxima over `P`); such a box exists exactly when `P` is bounded, so "P bounded" is
implied by `hbox`. If `γ = 0` then `log(1/γ)` is Lean's `log 0 = 0` and `r̄ = 0`, matching the
paper's `log(1/γ) = +∞`. The data are real (a generalization of rational data). -/
theorem step4_steps_to_convergence {m n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hG : specRadius G < 1)
    (h0 : (0 : Fin n → ℝ) ∈ interior (polyhedron A b))
    (M : Matrix (Fin n) (Fin n) ℝ) (hL : Gᵀ * M * G - M = -1)
    (l u : Fin n → ℝ) (hbox : polyhedron A b ⊆ Set.Icc l u) :
    ⌈Real.log (alpha2 M l u / alpha1 M A b) / Real.log (1 / gamma M)⌉₊ ≤
        ⌈(alpha2 M l u / alpha1 M A b - 1) / (1 - gamma M)⌉₊ ∧
      feasibleSet A b G =
        outerApprox A b G ⌈(alpha2 M l u / alpha1 M A b - 1) / (1 - gamma M)⌉₊ ∧
      feasibleSet A b G =
        outerApprox A b G ⌈Real.log (alpha2 M l u / alpha1 M A b) / Real.log (1 / gamma M)⌉₊ := by sorry

end RobustToDynamics
