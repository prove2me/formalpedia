-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_wronskian_entire_zeros_eq_eigenvalues
-- name    : TeschlODE.SturmLiouville.wronskian_entire_zeros_eq_eigenvalues
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:26:38.719801+00:00
-- url     : https://prove2.me/theorems/13ac2c51-fa45-4c3a-8b19-08c0c69ceac9
-- title:
--   Lemma 5.9 — the Wronskian W(z) is entire and vanishes exactly at the eigenvalues of L
-- statement:
--   Assume (5.45) and fix $\alpha, \beta$. For $z \in \mathbb{C}$ let $u_a(z, \cdot)$ and $u_b(z, \cdot)$ be the solutions on $[a,b]$ of $L u = z u$ (equivalently of (5.43)) with the initial conditions
--   $$u_a(z, a) = \sin\alpha,\quad p(a) u_a'(z, a) = \cos\alpha, \qquad u_b(z, b) = \sin\beta,\quad p(b) u_b'(z, b) = \cos\beta. \qquad (5.62)$$
--   Then the Wronskian
--   $$W(z) = W(u_b(z), u_a(z)) \qquad (5.61)$$
--   is an entire function of $z$, and $W(z) = 0$ if and only if $z$ is an eigenvalue of $L$ on $D(L)$.
--
--   The zeros of $W$ are therefore the eigenvalues, which is how the book obtains their discreteness (zeros of an entire function do not accumulate) and the existence of the resolvent for $W(z) \ne 0$.
--
--   **Formalization Note.** $u_a, u_b$ are families `ℂ → ℝ → ℂ` assumed to be $C^2$ on $[a,b]$ and to satisfy the equation and (5.62) for every $z$; such families exist and are unique, so the hypotheses are satisfiable and determine them. The Wronskian is evaluated at an arbitrary point $x_0 \in [a,b]$ (it is independent of $x_0$); the conclusion holds for each $x_0$. "Entire" is `Differentiable ℂ`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 158, Lemma 5.9

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_RegularSL
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_IsSLEigenfunction
import Definitions.Def_TeschlODE_SturmLiouville_SLWronskian

namespace TeschlODE.SturmLiouville

/-- Teschl, Lemma 5.9, p. 158: under (5.45), let `u_a(z, ·)`, `u_b(z, ·)` be the solutions of
`L u = z u` (5.43) on `[a, b]` with the initial conditions (5.62)
`u_a(z, a) = sin α`, `p(a) u_a′(z, a) = cos α`, `u_b(z, b) = sin β`, `p(b) u_b′(z, b) = cos β`.
Then the Wronskian `W(z) = W(u_b(z), u_a(z))` (5.61), evaluated at any point `x₀ ∈ [a, b]`, is an
entire function of `z` which vanishes precisely at the eigenvalues of `L`. -/
theorem wronskian_entire_zeros_eq_eigenvalues {p q r : ℝ → ℝ} {a b α β : ℝ}
    (hreg : RegularSL p q r a b) (ua ub : ℂ → ℝ → ℂ)
    (hua : ∀ z : ℂ, ContDiffOn ℝ 2 (ua z) (Set.Icc a b) ∧
      (∀ x ∈ Set.Icc a b, SLOp p q r a b (ua z) x = z * ua z x) ∧
      ua z a = (Real.sin α : ℂ) ∧
      (p a : ℂ) * derivWithin (ua z) (Set.Icc a b) a = (Real.cos α : ℂ))
    (hub : ∀ z : ℂ, ContDiffOn ℝ 2 (ub z) (Set.Icc a b) ∧
      (∀ x ∈ Set.Icc a b, SLOp p q r a b (ub z) x = z * ub z x) ∧
      ub z b = (Real.sin β : ℂ) ∧
      (p b : ℂ) * derivWithin (ub z) (Set.Icc a b) b = (Real.cos β : ℂ))
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc a b) :
    Differentiable ℂ (fun z => SLWronskian p a b (ub z) (ua z) x₀) ∧
      ∀ z : ℂ, SLWronskian p a b (ub z) (ua z) x₀ = 0 ↔
        ∃ f : ℝ → ℂ, IsSLEigenfunction p q r a b α β z f := by sorry

end TeschlODE.SturmLiouville
