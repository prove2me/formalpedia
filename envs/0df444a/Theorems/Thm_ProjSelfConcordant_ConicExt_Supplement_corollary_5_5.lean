-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_Supplement_corollary_5_5
-- name    : ProjSelfConcordant.ConicExt.Supplement.corollary_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:26:51.244032+00:00
-- url     : https://prove2.me/theorems/74538a4e-51bc-4e7a-aaab-7ff540359bef
-- title:
--   Corollary 5.5, p. 15 — the dual f∗ satisfies projective self-concordance with the same parameter γ
-- statement:
--   Let $X\subset\mathbb R^n$ be a regular convex set and $f$ a projectively self-concordant barrier on $X$ with parameter $\gamma$. Then the dual function $f_*(p)=-\min_{x\in X^o}\bigl(f(x)+\log(1+\langle x,p\rangle)\bigr)$ satisfies the projective self-concordance conditions with the same parameter $\gamma$ on its domain of definition $\operatorname{dom}f_*$: this domain is open, $f_*$ is $C^3$ on it, and for all $p\in\operatorname{dom}f_*$ and all $h$,
--   $$f_*''(p)[h,h]-(f_*'(p)[h])^2>0\quad(h\ne0),$$
--   $$\bigl|f_*'''(p)[h,h,h]-6f_*''(p)[h,h]f_*'(p)[h]+4(f_*'(p)[h])^3\bigr|\le2\gamma\bigl(f_*''(p)[h,h]-(f_*'(p)[h])^2\bigr)^{3/2}.$$
--
--   Together with Theorem 5.6 this is the duality theory for projectively self-concordant barriers.
--
--   **Formalization Note** Conditions (1) and (3) are the published predicates `ProjCond1`, `ProjCond3`. The condition-(3) power $3/2$ is `Real.rpow`, applied to a base that condition (1) makes nonnegative.
--
--   Differences from the source:
--   - reading: "a similar condition on the dual function" → conditions (1) and (3) of Definition 1.4 with parameter γ on dom f∗, together with openness of dom f∗ and C³ regularity of f∗ there; reason: Definition 1.4's conditions are stated for a C³ function on an open set, and the proof of Lemma 5.4 supplies both (dom f∗ is the image of an open set under the local diffeomorphism P, and f∗′(p) = −(1 + ⟨f′(x), x⟩)x is C²); the boundary condition (2) is the subject of Theorem 5.6, not of this corollary
--   - encoding: functions and derivatives on open subsets of ℝⁿ → total functions on EuclideanSpace ℝ (Fin n), with Fréchet derivatives evaluated on the stated open domains; reason: every source function extends outside its domain; derivatives at interior points depend only on local values, and the Euclidean inner product identifies covectors with gradients when needed
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 15, Corollary 5.5 (with Lemma 5.4, p. 13, and the paragraph after its proof)

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Duality

namespace ProjSelfConcordant.ConicExt.Supplement

/-- Corollary 5.5, p. 15: if `f` is a projectively self-concordant barrier with parameter `γ` on a
regular convex set `X`, then the dual function `f∗` is `C³` on its (open) domain of definition
and satisfies conditions (1) and (3) of Definition 1.4 there with the same parameter `γ`. -/
theorem corollary_5_5 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (γ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ProjBarrier γ X f) :
    IsOpen (dualDomain X f) ∧ ContDiffOn ℝ 3 (fstar X f) (dualDomain X f) ∧
      ProjCond1 (dualDomain X f) (fstar X f) ∧
      ProjCond3 γ (dualDomain X f) (fstar X f) := by sorry

end ProjSelfConcordant.ConicExt.Supplement
