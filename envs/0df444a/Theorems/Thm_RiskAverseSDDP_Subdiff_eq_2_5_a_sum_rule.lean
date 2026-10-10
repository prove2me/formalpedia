-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_eq_2_5_a_sum_rule
-- name    : RiskAverseSDDP.Subdiff.eq_2_5_a_sum_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T04:31:46.676518+00:00
-- url     : https://prove2.me/theorems/67492343-d943-4d58-aa1f-3fdb0634fffe
-- title:
--   (2.5)-(a) with (2.6), p. 4 — ∂(f + 𝕀_{Gr(S)})(z₀) = ∂f(z₀) + 𝒩_{Gr(S)}(z₀) when ri(dom f) ∩ ri(dom 𝕀_{Gr(S)}) ≠ ∅
-- statement:
--   Let $f$ be lower semicontinuous, proper and convex, let each $g_i$ be convex and lower semicontinuous with values in $\mathbb R\cup\{+\infty\}$, and let $Y$ be convex, so that $\operatorname{Gr}(S)=C_1\cap C_2\cap(\mathbb R^m\times Y)$ is convex. Let $z_0\in\operatorname{Gr}(S)$ with $f(z_0)<+\infty$, and assume (2.6):
--   $$\operatorname{ri}(\operatorname{dom}(f))\cap\operatorname{ri}(\operatorname{dom}(\mathbb I_{\operatorname{Gr}(S)}))\ne\emptyset.$$
--   Then
--   $$\partial\big(f+\mathbb I_{\operatorname{Gr}(S)}\big)(z_0)=\partial f(z_0)+\mathcal N_{\operatorname{Gr}(S)}(z_0),$$
--   that is, $u$ is a subgradient of $f+\mathbb I_{\operatorname{Gr}(S)}$ at $z_0$ exactly when $u=a+v$ with $a\in\partial f(z_0)$ and $v\in\mathcal N_{\operatorname{Gr}(S)}(z_0)$.
--
--   This is equivalence (2.5)-(a) of the proof of Lemma 2.1, the sum rule of Rockafellar's Theorem 23.8 applied to $f$ and the indicator of $\operatorname{Gr}(S)$. The page derives (2.6) from the Slater-type condition and (H); that derivation is where the printed lemma fails (see the mission description), so here (2.6) is a hypothesis, as the page states it.
--
--   **Formalization Note** The statement is for all $u\in\mathbb R^m\times\mathbb R^n$, which contains the case $u=(s,0)$ used on the page. $\operatorname{dom}(\mathbb I_{\operatorname{Gr}(S)})=\operatorname{Gr}(S)$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 4, proof of Lemma 2.1, (2.5)-(a) and (2.6)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Subdiff_Model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace

namespace RiskAverseSDDP.Subdiff

open ConvexProgram

/-- Equivalence (2.5)-(a) under (2.6), p. 4 (Rockafellar, Theorem 23.8): if `f` is proper,
convex and lower semicontinuous, the `g_i` are convex lower semicontinuous with values in
`ℝ ∪ {+∞}`, `Y` is convex, `z₀ ∈ Gr(S)`, `f(z₀) < +∞` and
`ri(dom f) ∩ ri(dom 𝕀_{Gr(S)}) ≠ ∅`, then `∂(f + 𝕀_{Gr(S)})(z₀) = ∂f(z₀) + 𝒩_{Gr(S)}(z₀)`. -/
theorem eq_2_5_a_sum_rule {m n q p : ℕ} (P : ConvexProgram m n q p)
    (hf : LowerSemicontinuous P.f ∧ RiskAverseSDDP.Convergence.EProper P.f ∧ RiskAverseSDDP.Convergence.EConvex P.f)
    (hg : ∀ i, LowerSemicontinuous (P.g i) ∧ RiskAverseSDDP.Convergence.EConvex (P.g i) ∧ ∀ z, P.g i z ≠ ⊥)
    (hY : Convex ℝ P.Y)
    (z₀ : E m × E n) (hz₀ : z₀ ∈ P.GrS) (hfz₀ : P.f z₀ ≠ ⊤)
    (h26 : (intrinsicInterior ℝ (edom P.f) ∩
      intrinsicInterior ℝ (edom (indicatorE P.GrS))).Nonempty) :
    ∀ u : E m × E n, u ∈ subdiffProd (fun z => P.f z + indicatorE P.GrS z) z₀ ↔
      ∃ a ∈ subdiffProd P.f z₀, ∃ v ∈ normalConeProd P.GrS z₀, u = a + v := by sorry

end RiskAverseSDDP.Subdiff
