-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P87_thinPath_groupoidLaws
-- name    : QAlgorithms.Papers.Independent.Intake100.P87.thinPath_groupoidLaws
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:28:44.35232+00:00
-- url     : https://prove2.me/theorems/a215088c-81de-4fa6-b953-fc5364fa5a95
-- title:
--   Thin path classes form a groupoid
-- statement:
--   Let $M$ be an ordinary finite-dimensional Hausdorff, second-countable real smooth manifold. A path is smooth, has sitting instants at both endpoints, and is taken modulo smooth homotopies whose differential has rank at most one everywhere, with the boundary collars of Definition 2.2. Write $[\gamma]$ for its thin class, $\mathrm{id}_x$ for the constant path at $x$, and $\gamma^{-1}(t)=\gamma(1-t)$ for reversal. Concatenation traverses its right-hand argument first, using the two half intervals.
--
--   For every path $\gamma:x\to y$ and all further paths $\gamma':y\to z$, $\gamma'':z\to w$,
--
--   $$
--   [\gamma\circ\mathrm{id}_x]=[\gamma]=[\mathrm{id}_y\circ\gamma],\qquad
--   [(\gamma''\circ\gamma')\circ\gamma]=[\gamma''\circ(\gamma'\circ\gamma)],
--   $$
--   $$
--   [\gamma\circ\gamma^{-1}]=[\mathrm{id}_y],\qquad
--   [\gamma^{-1}\circ\gamma]=[\mathrm{id}_x].
--   $$
--
--   These identities give the unit, associativity, and inverse laws for the thin path groupoid. No connectedness or nonemptiness assumption is imposed.
--
--   **Formalization Note** Representative expressions are evaluated by the printed concatenation and reversal formulas before quotienting by geometric thin homotopy. The equalities concern classes, not raw parameterized paths.
-- source:
--   Parallel Transport and Functors, arXiv:0705.0452v5, PDF p. 8, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P87

noncomputable section

open scoped ContDiff Manifold

namespace QAlgorithms.Papers.Independent.Intake100.P87

universe u v

/-- Lemma 2.3(a,b,c), PDF pp. 8–9: all unit, associativity, and inverse identities
hold for thin classes of the source's specified concatenations and reversals. -/
theorem thinPath_groupoidLaws (M : SmoothManifold.{u}) {x y : M.carrier}
    (gamma : PathExpression M x y) :
    pathClass (.compose gamma (.constant x)) = pathClass gamma ∧
    pathClass (.compose (.constant y) gamma) = pathClass gamma ∧
    (∀ {z w : M.carrier} (delta : PathExpression M y z) (eta : PathExpression M z w),
      pathClass (.compose (.compose eta delta) gamma) =
        pathClass (.compose eta (.compose delta gamma))) ∧
    pathClass (.compose gamma (.reverse gamma)) = pathClass (.constant y) ∧
    pathClass (.compose (.reverse gamma) gamma) = pathClass (.constant x) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P87

end
