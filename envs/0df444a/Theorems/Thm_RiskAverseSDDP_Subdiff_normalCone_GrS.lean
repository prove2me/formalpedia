-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_normalCone_GrS
-- name    : RiskAverseSDDP.Subdiff.normalCone_GrS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:31:55.075542+00:00
-- url     : https://prove2.me/theorems/93c0f02f-a561-448b-8880-8672d63337b3
-- title:
--   Proof of Lemma 2.1, p. 4 — 𝒩_{Gr(S)} = 𝒩_{C₁} + 𝒩_{C₂} + 𝒩_{ℝ^m×Y} and 𝒩_{ℝ^m×Y}(x₀, y₀) = {0}×𝒩_Y(y₀)
-- statement:
--   Let each $g_i$ be convex and lower semicontinuous with values in $\mathbb R\cup\{+\infty\}$ (so $C_2=\{g\le 0\}$ is closed and convex), let $Y\subseteq\mathbb R^n$ be nonempty, compact and convex, and assume that some point lies in
--   $$\operatorname{ri}(C_2)\cap\operatorname{ri}(\mathbb R^m\times Y)\cap C_1 .$$
--   Then for every $z_0=(x_0,y_0)\in\operatorname{Gr}(S)=C_1\cap C_2\cap(\mathbb R^m\times Y)$,
--   $$\mathcal N_{\operatorname{Gr}(S)}(x_0,y_0)=\mathcal N_{C_1}(x_0,y_0)+\mathcal N_{C_2}(x_0,y_0)+\mathcal N_{\mathbb R^m\times Y}(x_0,y_0),$$
--   and
--   $$\mathcal N_{\mathbb R^m\times Y}(x_0,y_0)=\{0\}\times\mathcal N_Y(y_0).$$
--
--   This is the normal-cone calculus step of the proof of Lemma 2.1 (Rockafellar, Corollary 23.8.1, with $C_1$ affine). The constraint qualification is the one printed on the page for this step.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 4, proof of Lemma 2.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- Proof of Lemma 2.1, p. 4: if the `g_i` are convex lower semicontinuous with values in
`ℝ ∪ {+∞}`, `Y` is nonempty, compact and convex, and some point lies in
`ri(C₂) ∩ ri(ℝ^m × Y) ∩ C₁`, then at every `z₀ ∈ Gr(S)`
`𝒩_{Gr(S)}(z₀) = 𝒩_{C₁}(z₀) + 𝒩_{C₂}(z₀) + 𝒩_{ℝ^m×Y}(z₀)` and
`𝒩_{ℝ^m×Y}(z₀) = {0} × 𝒩_Y(y₀)`. -/
theorem normalCone_GrS {m n q p : ℕ} (P : ConvexProgram m n q p)
    (hg : ∀ i, LowerSemicontinuous (P.g i) ∧ RiskAverseSDDP.Convergence.EConvex (P.g i) ∧ ∀ z, P.g i z ≠ ⊥)
    (hY : P.Y.Nonempty ∧ IsCompact P.Y ∧ Convex ℝ P.Y)
    (hqual : (intrinsicInterior ℝ P.C2 ∩ intrinsicInterior ℝ (Set.univ ×ˢ P.Y) ∩
      P.C1).Nonempty)
    (z₀ : E m × E n) (hz₀ : z₀ ∈ P.GrS) :
    normalConeProd P.GrS z₀ =
        {v | ∃ v₁ ∈ normalConeProd P.C1 z₀, ∃ v₂ ∈ normalConeProd P.C2 z₀,
          ∃ v₃ ∈ normalConeProd (Set.univ ×ˢ P.Y) z₀, v = v₁ + v₂ + v₃} ∧
      normalConeProd (Set.univ ×ˢ P.Y) z₀ =
        {v | v.1 = 0 ∧ v.2 ∈ FirstOrderOpt.ConvexTheory.normalCone P.Y z₀.2} := by sorry

end RiskAverseSDDP.Subdiff
