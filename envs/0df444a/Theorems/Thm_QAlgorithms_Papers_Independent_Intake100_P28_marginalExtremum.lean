-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_marginalExtremum
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.marginalExtremum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:31:58.497518+00:00
-- url     : https://prove2.me/theorems/dbed18c2-6568-45f7-82f7-e24440ae8f5d
-- title:
--   Lemma 2.3: marginal infimum of a jointly convex function
-- statement:
--   Let $E,F$ be real vector spaces and let $S\subseteq E$, $T\subseteq F$ be convex, with $T$ nonempty. Let $f:S\times T\to\mathbb R$.
--
--   1. If $f$ is jointly convex and each fiber $\{f(x,y):y\in T\}$ is bounded below, then its marginal infimum is convex.
--   2. If $f$ is jointly concave and each fiber is bounded above, then its marginal supremum is concave.
--
--   In formulas,
--   $$
--   g(x)=\inf_{y\in T}f(x,y)\text{ is convex},\qquad
--   h(x)=\sup_{y\in T}f(x,y)\text{ is concave},
--   $$
--   under the respective hypotheses. Fiber extrema are finite real numbers; attainment is not required.
--
--   This is the marginal-extremum principle cited to Rockafellar [19], Theorem 1, and proved in the paper.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 9, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.3, PDF p.9, Rockafellar [19], Theorem 1. Finite-valued fibers
are nonempty and bounded on the appropriate side, as its epsilon proof requires. -/
theorem marginalExtremum
    {E F : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (S : Set E) (T : Set F) (hS : Convex ℝ S) (hT : Convex ℝ T) (hne : T.Nonempty)
    (f : E × F → ℝ) :
    ((ConvexOn ℝ (S ×ˢ T) f ∧
      ∀ x ∈ S, BddBelow (Set.range fun y : T => f (x,y))) →
      ConvexOn ℝ S (fun x => sInf (Set.range fun y : T => f (x,y)))) ∧
    ((ConcaveOn ℝ (S ×ˢ T) f ∧
      ∀ x ∈ S, BddAbove (Set.range fun y : T => f (x,y))) →
      ConcaveOn ℝ S (fun x => sSup (Set.range fun y : T => f (x,y)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
