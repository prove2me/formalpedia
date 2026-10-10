-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_eq_2_5_inf_projection
-- name    : RiskAverseSDDP.Subdiff.eq_2_5_inf_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:32:04.074986+00:00
-- url     : https://prove2.me/theorems/3828f7d4-f996-48ee-8fce-8bff46eaedf3
-- title:
--   (2.5), first equivalence, p. 4 — 𝒬 = inf_y (f + 𝕀_{Gr(S)}) and s ∈ ∂𝒬(x₀) ⇔ (s, 0) ∈ ∂(f + 𝕀_{Gr(S)})(x₀, y₀)
-- statement:
--   Let $f$, $g$, $A$, $B$, $b$, $Y$ be the data of the program (2.1), with $f$ never equal to $-\infty$, and let $\operatorname{Gr}(S)=\{(x,y): Ax+By=b,\ g(x,y)\le 0,\ y\in Y\}$. Then for every $x\in\mathbb R^m$
--   $$\mathcal Q(x)=\inf_{y\in\mathbb R^n}\ f(x,y)+\mathbb I_{\operatorname{Gr}(S)}(x,y).$$
--   Moreover, if $y_0\in\operatorname{Sol}(x_0)$ and $f(x_0,y_0)<+\infty$, then for every $s\in\mathbb R^m$
--   $$s\in\partial\mathcal Q(x_0)\iff (s,0)\in\partial\big(f+\mathbb I_{\operatorname{Gr}(S)}\big)(x_0,y_0).$$
--
--   This is the first step of the proof of Lemma 2.1 (Rockafellar, *Convex Analysis*, Theorem 24(a)): a subgradient of an infimal projection is read off from the joint function at a minimizer, with zero $y$-component.
--
--   **Formalization Note** The hypotheses are those this step uses: $f>-\infty$ everywhere (part of "proper" in (H)), $y_0\in\operatorname{Sol}(x_0)$ and $f(x_0,y_0)=\mathcal Q(x_0)$ finite. Under the hypotheses of Lemma 2.1 these hold. The sum $f+\mathbb I_{\operatorname{Gr}(S)}$ is computed in `EReal`; since $f\ne-\infty$, it equals $+\infty$ off $\operatorname{Gr}(S)$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 4, proof of Lemma 2.1, (2.5) first equivalence

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- Proof of Lemma 2.1, p. 4, and the first equivalence of (2.5) (Rockafellar, Theorem 24(a)):
`𝒬(x) = inf_y f(x, y) + 𝕀_{Gr(S)}(x, y)` for every `x`, and for `y₀ ∈ Sol(x₀)` with
`f(x₀, y₀)` finite, `s ∈ ∂𝒬(x₀) ⇔ (s, 0) ∈ ∂(f + 𝕀_{Gr(S)})(x₀, y₀)`. -/
theorem eq_2_5_inf_projection {m n q p : ℕ} (P : ConvexProgram m n q p)
    (hf : ∀ z, P.f z ≠ ⊥)
    (x₀ : E m) (y₀ : E n) (hy₀ : y₀ ∈ P.Sol x₀) (hfin : P.f (x₀, y₀) ≠ ⊤) :
    (∀ x : E m, P.Q x = ⨅ y : E n, (P.f (x, y) + indicatorE P.GrS (x, y))) ∧
    ∀ s : E m, s ∈ subdiff P.Q x₀ ↔
      (s, (0 : E n)) ∈ subdiffProd (fun z => P.f z + indicatorE P.GrS z) (x₀, y₀) := by sorry

end RiskAverseSDDP.Subdiff
