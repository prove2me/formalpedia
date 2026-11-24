-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_Supplement_theorem_c_3
-- name    : SparseLpLq.SmallP.Supplement.theorem_c_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:16:23.184102+00:00
-- url     : https://prove2.me/theorems/48ab8260-efc6-4fa7-80c0-9add44aafb95
-- title:
--   Theorem C.3 — for λ ≥ c(n^{p/2−1}ϵ)^{−1/p}‖x̃‖_p^p, the projection onto FEA(A,b,σ,1) of any global minimizer of F_λ is an ϵ-minimizer of (1.4)
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, and the blanket assumptions of the paper (p. 1) hold for $q=1$: $\sigma\ge 0$, $\mathrm{FEA}(A,b,\sigma,1)=\{x:\|Ax-b\|_1\le\sigma\}\neq\emptyset$ and $\|b\|_1>\sigma$. Let $0<p<1$ and $F_\lambda(x)=\|x\|_p^p+\lambda(\|Ax-b\|_1-\sigma)_+$ (3.3).
--
--   Let $\tilde x\in\mathrm{FEA}(A,b,\sigma,1)$ be any feasible point, $\epsilon>0$, and $c>0$ a constant as in Lemma C.3, i.e. $\mathrm{dist}(x,\mathrm{FEA}(A,b,\sigma,1))\le c(\|Ax-b\|_1-\sigma)_+$ for all $x$. Let
--   $$\lambda\ \ge\ c\,\big(n^{\frac p2-1}\epsilon\big)^{-\frac1p}\,\|\tilde x\|_p^p ,$$
--   and let $x^*_\lambda$ be any global minimizer of $F_\lambda$. Then the Euclidean projection $\mathcal P_{\mathrm{FEA}(A,b,\sigma,1)}(x^*_\lambda)$ exists and is an $\epsilon$-minimizer of (1.4) (Definition C.1(i)): it is feasible and
--   $$\big\|\mathcal P_{\mathrm{FEA}(A,b,\sigma,1)}(x^*_\lambda)\big\|_p^p\ \le\ \min\{\|x\|_p^p: x\in\mathrm{FEA}(A,b,\sigma,1)\}+\epsilon .$$
--
--   The theorem turns any global solution of the unconstrained penalty problem, even an infeasible one, into a near-optimal feasible point, with an explicit penalty threshold.
--
--   **Formalization Note** "$c$ chosen as in Lemma C.3" is a hypothesis on $c$. The projection is characterized as a feasible point nearest to $x^*_\lambda$ in $\|\cdot\|_2$; the statement asserts that such a point exists and that every such point (there is exactly one) is an $\epsilon$-minimizer. The minimum in Definition C.1(i) is written as a bound against every feasible point. Under the blanket assumptions $\tilde x\ne0$, so the threshold is positive and $\lambda>0$ as (3.3) requires.
--
--   Differences from the source:
--   - encoding: c > 0 chosen as in Lemma C.3 → any c > 0 with distFEA x ≤ c(‖Ax − b‖₁ − σ)₊ for all x, as a hypothesis; reason: this is what 'as in Lemma C.3' fixes about c
--   - encoding: the projection 𝒫_FEA(A,b,σ,1)(x*_λ) → (∃ y, IsProjFEA x*_λ y) ∧ ∀ y, IsProjFEA x*_λ y → …, IsProjFEA = Euclidean nearest feasible point; reason: FEA(A,b,σ,1) is nonempty, closed and convex, so the nearest point exists and is unique; the notation 𝒫 presupposes this
--   - encoding: ‖x_ϵ‖_p^p ≤ min{‖x‖_p^p : x ∈ FEA(A,b,σ,1)} + ϵ (Definition C.1(i)) → ∀ y ∈ FEA(A,b,σ,1), ‖x_ϵ‖_p^p ≤ ‖y‖_p^p + ϵ; reason: equivalent; the minimum exists (§1, p. 1)
--   - encoding: λ > 0 in (3.3) → no separate hypothesis; λ ≥ the threshold; reason: under the blanket assumptions x̃ ≠ 0, so the threshold and hence λ are positive; no instance changes
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 27, Theorem C.3 (Definition C.1 p. 26; Lemma C.3 p. 25); proof p. 27

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

namespace SparseLpLq.SmallP.Supplement
open SparseLpLq.SmallP
theorem theorem_c_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (xt : Fin n → ℝ) (hxt : xt ∈ FEA A b σ 1) (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : 0 < c)
    (hcC3 : ∀ x : Fin n → ℝ, distFEA A b σ x ≤ c * max (qNorm 1 (A *ᵥ x - b) - σ) 0)
    (lam : ℝ) (hlam : c * ((n : ℝ) ^ (p / 2 - 1) * ε) ^ (-1 / p) * lpObj p xt ≤ lam)
    (xlam : Fin n → ℝ) (hxlam : ∀ y : Fin n → ℝ, Fpen A b σ p lam xlam ≤ Fpen A b σ p lam y) :
    (∃ y, IsProjFEA A b σ xlam y) ∧
      ∀ y, IsProjFEA A b σ xlam y → IsEpsMin14 A b σ p ε y := by sorry
end SparseLpLq.SmallP.Supplement
