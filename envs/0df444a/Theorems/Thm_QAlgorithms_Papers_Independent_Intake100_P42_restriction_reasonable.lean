-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_restriction_reasonable
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.restriction_reasonable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:21:45.796805+00:00
-- url     : https://prove2.me/theorems/99454011-b845-4e08-9107-514c09dee0ae
-- title:
--   Restriction of a uniform induced operator norm is a reasonable crossnorm
-- statement:
--   Let $\mathbb F$ be $\mathbb R$ or $\mathbb C$, and let $\alpha$ be one family of reasonable crossnorms on all normed pairs over $\mathbb F$ with the metric mapping property for every pair of bounded linear maps. Let $X,Y,V,W$ be arbitrary normed spaces. For an algebraic operator tensor $L\in\mathcal B(X,V)\otimes\mathcal B(Y,W)$, let $\rho_\alpha(L)$ be the actual induced norm of its canonical action from $X\otimes_\alpha Y$ to $V\otimes_\alpha W$. Then this norm is finite and
--
--   $$\|L\|_\varepsilon\le\rho_\alpha(L)\le\|L\|_\pi.$$
--
--   Moreover, $\rho_\alpha$ is a genuine reasonable crossnorm on the operator tensor product: it satisfies the norm axioms, the pure-tensor upper bound, and the continuity and norm bounds for every product of continuous dual functionals of the two operator factors. Both tensor norms in the displayed inequalities are those of the operator factors, using their standard operator norms. The case $V=X$, $W=Y$ is the Abstract's assertion for operator algebras. No completion or nonzero-dimension assumption is imposed.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 5, Theorem 4.1(a,b), with the Abstract operator-algebra specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF pp.5--6, Theorem 4.1(a,b), including the Abstract by V=X and W=Y.
Both inequalities and genuine reasonableness are retained. The induced norm
is the canonical action norm, not an independently chosen crossnorm. -/
theorem restriction_reasonable (a : CrossnormFamily F) (ha : IsUniform a)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W] :
    (∀ L : TensorProduct F (X →L[F] V) (Y →L[F] W),
      extendedOperatorNorm (a.norm X Y) (a.norm V W) (operatorAction L) < ⊤ ∧
      injectiveNorm L ≤ restrictedOperatorNorm (a.norm X Y) (a.norm V W) L ∧
      restrictedOperatorNorm (a.norm X Y) (a.norm V W) L ≤ algebraicProjectiveNorm L) ∧
    ReasonableCrossnorm (restrictedOperatorNorm (a.norm X Y) (a.norm V W)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
