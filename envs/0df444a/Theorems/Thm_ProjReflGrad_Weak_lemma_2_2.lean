-- Prove2me | Theorems.Thm_ProjReflGrad_Weak_lemma_2_2
-- name    : ProjReflGrad.Weak.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:50.320405+00:00
-- url     : https://prove2.me/theorems/904d176d-f0b9-4e85-93c6-2e49489b51fc
-- title:
--   Lemma 2.2 (Minty), p. 3 — for continuous monotone F, solutions of (1.1) are the solutions of the dual VI
-- statement:
--   Let $H$ be a real inner product space, $C\subseteq H$ convex, and $F:H\to H$ continuous on $C$ and monotone on $C$, i.e. $\langle F(x)-F(y),x-y\rangle\ge0$ for all $x,y\in C$. Then $x^*$ is a solution of (1.1), that is $x^*\in C$ and $\langle F(x^*),x-x^*\rangle\ge0$ for all $x\in C$, if and only if $x^*$ solves
--   $$\text{find }x\in C\text{ such that }\langle F(y),y-x\rangle\ge0\qquad\forall y\in C .$$
--
--   The dual formulation is linear in $x$, which makes it stable under weak limits; it is how weak cluster points of the iterates are shown to be solutions.
--
--   **Formalization Note.** The paper takes $F:C\to H$; here $F$ is defined on all of $H$ and only its restriction to $C$ is constrained. Convexity of $C$ is the standing assumption of (1.1). Closedness and completeness are not needed and not assumed.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 3, Lemma 2.2 (Minty)

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Weak

/-- Lemma 2.2 (Minty) (Malitsky 2015, p. 3): for `C` convex and `F` continuous and monotone on `C`,
`x*` solves (1.1) iff `x* ∈ C` and `⟨F(y), y - x*⟩ ≥ 0` for all `y ∈ C`. -/
theorem lemma_2_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCcv : Convex ℝ C) (F : H → H) (hcont : ContinuousOn F C)
    (hmono : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (F x - F y) (x - y)) (xs : H) :
    xs ∈ solSet C F ↔ xs ∈ C ∧ ∀ y ∈ C, 0 ≤ inner ℝ (F y) (y - xs) := by sorry

end ProjReflGrad.Weak
