-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_solSet_subsingleton
-- name    : ProjReflGrad.Linear.solSet_subsingleton
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:01.118164+00:00
-- url     : https://prove2.me/theorems/8656da80-2434-495c-9ff6-5c47d8a733a2
-- title:
--   Proof of Theorem 3.3, p. 6 — under strong monotonicity the variational inequality has at most one solution
-- statement:
--   Let $H$ be a real inner product space, $C\subseteq H$ any set, and $F:H\to H$ strongly monotone with modulus $m>0$, that is $\langle F(x)-F(y),x-y\rangle\ge m\|x-y\|^2$ for all $x,y\in H$. Then the variational inequality (1.1),
--   $$\text{find } x^*\in C \text{ with } \langle F(x^*),\,x-x^*\rangle\ge0\ \text{ for all } x\in C,$$
--   has at most one solution: if $x^*,\bar x\in S$ then $x^*=\bar x$.
--
--   Together with the existence assumption (C1) this is the uniqueness of the solution $z$ that Theorem 3.3 refers to as "the solution of (1.1)".
--
--   **Formalization Note.** Only strong monotonicity is used; closedness and convexity of $C$, completeness of $H$ and Lipschitz continuity are not hypotheses, which makes the statement more general than the context in which the paper uses it.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 6, proof of Theorem 3.3 (first sentence)

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Proof of Theorem 3.3 (Malitsky 2015, p. 6), first line: if `F` is strongly monotone with
modulus `m > 0` (C2*), the variational inequality (1.1) has at most one solution. -/
theorem solSet_subsingleton {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (m : ℝ) (hm : 0 < m) (hC2s : IsStronglyMonotoneMap F m) :
    (ProjReflGrad.Weak.solSet C F).Subsingleton := by sorry

end ProjReflGrad.Linear
