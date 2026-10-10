-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_normalCone_C2
-- name    : RiskAverseSDDP.Subdiff.normalCone_C2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:32:18.733248+00:00
-- url     : https://prove2.me/theorems/df631178-3d9c-4cc1-b787-4933e2ca7f29
-- title:
--   Proof of Lemma 2.1, p. 4 (repaired: real-valued g, strict Slater point) — 𝒩_{C₂}(z₀) = {Σ_{i∈I(z₀)} μ_i ∂g_i(z₀) : μ_i ≥ 0}
-- statement:
--   Let $g_1,\dots,g_p:\mathbb R^m\times\mathbb R^n\to\mathbb R$ be **real-valued** convex functions (convex, lower semicontinuous, finite everywhere) and assume there is a point $\bar z$ with $g_i(\bar z)<0$ for every $i$. Let $C_2=\{z: g_i(z)\le 0 \text{ for all } i\}$ and $z_0\in C_2$, with active set $I(z_0)=\{i: g_i(z_0)=0\}$. Then
--   $$\mathcal N_{C_2}(z_0)=\Big\{\sum_{i\in I(z_0)}\mu_i w_i:\ \mu_i\ge 0,\ w_i\in\partial g_i(z_0)\Big\}.$$
--
--   This is the last normal-cone formula of the proof of Lemma 2.1, which supplies the term $\{\sum_{i\in I}\mu_i\partial g_i(x_0,y_0):\mu_i\ge0\}$ of (2.4).
--
--   **Formalization Note (repair).** The page derives this formula from $(\bar x,\bar y)\in\operatorname{ri}(C_2)$ alone, with $g_i$ extended-valued. That is false: for $g(x,y)=y^2$ on $\mathbb R\times\mathbb R$, $C_2=\mathbb R\times\{0\}$ equals its own relative interior, yet $\mathcal N_{C_2}(0,0)=\{0\}\times\mathbb R$ while the right-hand side is $\{0\}$. The statement therefore assumes (R1) real-valued $g_i$ and (R2) a strict Slater point for $g$. In Lean (R1) is "$g_i\ne\pm\infty$" together with (H)-2, and $\mu$, $w$ are given as explicit witnesses indexed by $I(z_0)$ (so no Minkowski sum $0\cdot\partial g_i$ with an empty set arises).
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 4, proof of Lemma 2.1 (repaired hypotheses)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- Proof of Lemma 2.1, p. 4, repaired: if every `g_i` is a real-valued convex function
(convex, lower semicontinuous, never `±∞`) and some point `z̄` has `g_i(z̄) < 0` for every
`i` (strict Slater point), then at every `z₀ ∈ C₂ = {g ≤ 0}`
`𝒩_{C₂}(z₀) = {Σ_{i ∈ I(z₀)} μ_i w_i : μ_i ≥ 0, w_i ∈ ∂g_i(z₀)}`. -/
theorem normalCone_C2 {m n q p : ℕ} (P : ConvexProgram m n q p)
    (hg : ∀ i, LowerSemicontinuous (P.g i) ∧ RiskAverseSDDP.Convergence.EConvex (P.g i) ∧ ∀ z, P.g i z ≠ ⊥)
    (hR1 : ∀ i z, P.g i z ≠ ⊤)
    (hR2 : ∃ zb : E m × E n, ∀ i, P.g i zb < 0)
    (z₀ : E m × E n) (hz₀ : z₀ ∈ P.C2) :
    normalConeProd P.C2 z₀ =
      {v | ∃ μ : Fin p → ℝ, ∃ w : Fin p → E m × E n,
        (∀ i ∈ P.active z₀.1 z₀.2, 0 ≤ μ i ∧ w i ∈ subdiffProd (P.g i) z₀) ∧
        v = ∑ i ∈ P.active z₀.1 z₀.2, μ i • w i} := by sorry

end RiskAverseSDDP.Subdiff
