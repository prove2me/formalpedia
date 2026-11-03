-- Prove2me | Theorems.Thm_TrustIPM_lemma_2
-- name    : TrustIPM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:45.471316+00:00
-- url     : https://prove2.me/theorems/2d752f89-d6e9-4d51-ab43-07d5b700819c
-- title:
--   Lemma 2 — Lipschitz $p$th derivatives iff $|g^{(p+1)}|\le L_p$ on an open set
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be $p+1$ times differentiable on an open set $S\subseteq\mathbb R$ and let $L_p\in(0,\infty)$. Then $g$ has $L_p$-Lipschitz $p$th derivatives on $S$ (Definition 1) if and only if
--
--   $$
--   \bigl|g^{(p+1)}(\theta)\bigr|\le L_p\qquad\text{for all }\theta\in S .
--   $$
--
--   The lemma converts the directional Lipschitz conditions of Assumption 1 into derivative bounds on the open set $\mathcal X$, for instance $\|\nabla^2 f(x)\|_2\le L_1$.
--
--   **Formalization Note** "$p+1$ times differentiable on $S$" means that $g,g',\dots,g^{(p)}$ are differentiable at every point of $S$.
--
--   Differences from the source:
--   - reading: g is p + 1 order differentiable on the open set S → iteratedDeriv k g is differentiable at every point of S for every k ≤ p; reason: the page leaves the meaning implicit; this is the classical one
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Lemma 2, p.4

import Mathlib
import Definitions.Def_TrustIPM_HasLipDerivOn

namespace TrustIPM

/-- **Lemma 2** (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Lemma 2, p.4). A univariate function `g : ℝ → ℝ` that is
`p + 1` order differentiable on the open set `S ⊆ ℝ` has `L_p`-Lipschitz `p`th order derivatives on
`S` if and only if `|g⁽ᵖ⁺¹⁾(θ)| ≤ L_p` for all `θ ∈ S`.

**Formalization Note** "`p + 1` order differentiable on `S`": `g, g′, …, g⁽ᵖ⁾` are differentiable at
every point of `S`. `L_p ∈ (0, ∞)` is the frame of Definition 1. -/
theorem lemma_2 (g : ℝ → ℝ) (p : ℕ) (L : ℝ) (S : Set ℝ) (hL : 0 < L) (hS : IsOpen S)
    (hdiff : ∀ k ≤ p, ∀ θ ∈ S, DifferentiableAt ℝ (iteratedDeriv k g) θ) :
    HasLipDerivOn p L g S ↔ ∀ θ ∈ S, |iteratedDeriv (p + 1) g θ| ≤ L := by sorry

end TrustIPM
