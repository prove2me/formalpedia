-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_sup_norm_bound
-- name    : TeschlQM.OneParticle.sup_norm_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T08:02:56.68945+00:00
-- url     : https://prove2.me/theorems/d1063955-7475-4d4e-9fe5-94582cc32971
-- title:
--   Lemma 10.1 — H²(ℝⁿ) ⊆ C_∞(ℝⁿ) with ‖ψ‖_∞ ≤ a‖H₀ψ‖ + b‖ψ‖ for n ≤ 3
-- statement:
--   Let $n \le 3$ and let $H_0 = -\Delta$ with domain $H^2(\mathbb R^n)$. Every $\psi \in H^2(\mathbb R^n)$ lies in $C_\infty(\mathbb R^n)$, i.e. it has a continuous representative vanishing at infinity. Moreover, for any $a > 0$ there is a $b > 0$ such that for all $\psi \in H^2(\mathbb R^n)$
--   $$\|\psi\|_\infty \le a \|H_0 \psi\| + b \|\psi\|,$$
--   where $\|\psi\|_\infty$ is the supremum of the continuous representative.
--
--   This says that multiplication by a bounded function, and by an $L^2$ function in low dimension, is $H_0$-bounded with bound $0$; it is the first step of Theorem 10.2.
--
--   **Formalization Note.** $C_\infty(\mathbb R^n)$ is Mathlib's `ℝⁿ →C₀ ℂ` with its sup norm; the bound is asserted for every such representative of $\psi$ (the continuous representative is unique). The constant $b$ depends only on $a$ and $n$, not on $\psi$, as in the book's proof.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 221, Lemma 10.1

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian

namespace TeschlQM.OneParticle

open MeasureTheory
open scoped ZeroAtInfty

/-- Teschl, Lemma 10.1, p. 221. Suppose `n ≤ 3` and `ψ ∈ H²(ℝⁿ)`. Then `ψ ∈ C_∞(ℝⁿ)` (it has a
continuous representative vanishing at infinity, an element of `ℝⁿ →C₀ ℂ`), and for any `a > 0`
there is a `b > 0` such that `‖ψ‖_∞ ≤ a‖H₀ψ‖ + b‖ψ‖` (10.2), where `‖ψ‖_∞` is the sup norm of that
continuous representative. The constant `b` depends only on `a` (and `n`), not on `ψ`, as in the
book's proof. -/
theorem sup_norm_bound (n : ℕ) (hn : n ≤ 3) :
    (∀ ψ ∈ sobolevH2 n, ∃ f : EuclideanSpace ℝ (Fin n) →C₀ ℂ,
        (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] f) ∧
      ∀ a : ℝ, 0 < a → ∃ b : ℝ, 0 < b ∧
        ∀ (ψ : (freeHamiltonian n).domain) (f : EuclideanSpace ℝ (Fin n) →C₀ ℂ),
          ((ψ : L2 n) : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] f →
            ‖f‖ ≤ a * ‖freeHamiltonian n ψ‖ + b * ‖(ψ : L2 n)‖ := by sorry

end TeschlQM.OneParticle
