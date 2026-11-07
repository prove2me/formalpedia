-- Prove2me | Theorems.Thm_PNormReg_theorem_2_init
-- name    : PNormReg.theorem_2_init
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:38:55.346206+00:00
-- url     : https://prove2.me/theorems/57464cc8-c903-42c7-a53b-6775d8c6a732
-- title:
--   Proof of Theorem 2, p.20 — initialization and conversion: $f(x^{(0)})\le2^pn^{p/2-1}f^\star$ and $\log(2+\nu_0/\epsilon')=O(p\log(2n)+\log(1/\epsilon))$
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$, $p\ge2$, $\epsilon\in(0,1)$, and $f(x)=\|Ax-b\|_p^p$ with minimizer $x^\star$. Let $x^{(0)}$ be a 2-approximate solution of $\min_x\|Ax-b\|_2$ with $Ax^{(0)}\ne b$. Then
--
--   $$\|Ax^{(0)}-b\|_p\le\|Ax^{(0)}-b\|_2\le2\|Ax^\star-b\|_2\le2n^{1/2-1/p}\|Ax^\star-b\|_p.$$
--
--   Consequently:
--
--   1. $f(x^{(0)})\le2^pn^{p/2-1}f^\star$, and $\nu_0:=f(x^{(0)})$ is a valid initial gap bound;
--   2. $\epsilon':=\epsilon f(x^{(0)})/(2^pn^{p/2-1})\le\epsilon f^\star$;
--   3. any $x$ with $f(x)\le f^\star+\epsilon'$ has $f(x)\le(1+\epsilon)f^\star$ and $\|Ax-b\|_p\le(1+\epsilon)^{1/p}f^\star_p\le(1+\epsilon)f^\star_p$;
--   4. $\log(2+\nu_0/\epsilon')\le C(p\log(2n)+\log(1/\epsilon))$ for an absolute constant $C$.
--
--   This is how Theorem 2 follows from Theorem 9: the powered objective inherits a multiplicative guarantee, at a cost logarithmic in $n$ and $1/\epsilon$ and linear in $p$.
--
--   Differences from the source:
--   - encoding: "The total failure probability is at most δ" → not restated here; reason: it is δ/2 + δ/2 = δ; its probabilistic content is the goal PNormReg.theorem_2
--   - encoding: "= O(p log(2n) + log(1/ϵ))" → ∃ C > 0 absolute, chosen before all the data, with ≤ C·(p log(2n) + log(1/ϵ)); reason: the meaning of O(·)
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Proof of Theorem 2, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_PNormReg_Norms

open Matrix

namespace PNormReg

/-- **Proof of Theorem 2**, initialization and conversion, p.20 (PDF p.21).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

With `f(x) = ∥Ax − b∥_p^p`, `x⁽⁰⁾` a 2-approximate least-squares solution with `Ax⁽⁰⁾ ≠ b`, and `x⋆` a
minimizer of `f`: every link of the page's chain, and `log(2 + ν₀/ϵ′) ≤ C(p log(2n) + log(1/ϵ))`, for an
absolute `C` chosen before all the data.

**Formalization Note.** `ν₀ := f(x⁽⁰⁾)`, `ϵ′ := ϵf(x⁽⁰⁾)/(2^p n^{p/2−1})`. "It returns x satisfying" is
the implication from `f(x) ≤ f⋆ + ϵ′`. The page's failure-probability sentence is `δ/2 + δ/2 = δ`, whose
probabilistic content is `PNormReg.theorem_2`. -/
theorem theorem_2_init :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (p ε : ℝ)
        (x₀ xstar : Fin d → ℝ),
        Function.Injective A.mulVec → 2 ≤ p → 0 < ε → ε < 1 →
        (∀ x, l2Norm (A *ᵥ x₀ - b) ≤ 2 * l2Norm (A *ᵥ x - b)) →
        A *ᵥ x₀ ≠ b →
        (∀ x, lpPow p (A *ᵥ xstar - b) ≤ lpPow p (A *ᵥ x - b)) →
        let f : (Fin d → ℝ) → ℝ := fun x => lpPow p (A *ᵥ x - b)
        let ε' : ℝ := ε * f x₀ / (2 ^ p * (n : ℝ) ^ (p / 2 - 1))
        lpNorm p (A *ᵥ x₀ - b) ≤ l2Norm (A *ᵥ x₀ - b) ∧
        l2Norm (A *ᵥ x₀ - b) ≤ 2 * l2Norm (A *ᵥ xstar - b) ∧
        2 * l2Norm (A *ᵥ xstar - b) ≤ 2 * (n : ℝ) ^ (1 / 2 - 1 / p) * lpNorm p (A *ᵥ xstar - b) ∧
        f x₀ ≤ 2 ^ p * (n : ℝ) ^ (p / 2 - 1) * f xstar ∧
        f x₀ - f xstar ≤ f x₀ ∧
        ε' ≤ ε * f xstar ∧
        (∀ x, f x ≤ f xstar + ε' →
          f x ≤ (1 + ε) * f xstar ∧
          lpNorm p (A *ᵥ x - b) ≤ (1 + ε) ^ (1 / p) * lpNorm p (A *ᵥ xstar - b) ∧
          (1 + ε) ^ (1 / p) * lpNorm p (A *ᵥ xstar - b) ≤ (1 + ε) * lpNorm p (A *ᵥ xstar - b)) ∧
        Real.log (2 + f x₀ / ε') ≤ C * (p * Real.log (2 * n) + Real.log (1 / ε)) := by sorry

end PNormReg
