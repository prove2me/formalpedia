-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_strong_operator_product_rule
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.strong_operator_product_rule
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:09:40.117774+00:00
-- url     : https://prove2.me/theorems/9ef05ac3-eeb5-4823-ae4b-4430d2134854
-- title:
--   Product rule for a strongly continuous operator path
-- statement:
--   Let $E,F$ be real Banach spaces, $D\subseteq E$ a real linear subspace, and $I\subseteq\mathbb R$ an interval. Complex Banach spaces may be regarded as real spaces here. Let $K(t):E\to F$ be bounded linear operators such that $t\mapsto K(t)v$ is continuous on $I$ for every $v\in E$ and differentiable relative to $I$ for every $v\in D$. Let $\gamma:I\to E$ take its values in $D$ and have actual velocity $\dot\gamma(t)\in E$. Define $K'(t)v$ to be the relative derivative of $s\mapsto K(s)v$ at $t$. At every non-isolated parameter $t\in I$ where relative derivatives are unique,
--
--   $$
--   \frac{d}{dt}\bigl(K(t)\gamma(t)\bigr)=K'(t)\gamma(t)+K(t)\dot\gamma(t).
--   $$
--
--   The derivative is relative to the interval, including one-sided endpoint derivatives. Neither density of $D$ nor operator-norm continuity of $K$ is required. This rule permits differentiating products in the strong operator topology.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 3, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

/-- Lemma 4, PDF p.3: the strong-operator product rule. The derivative of K on
D is computed from K, while the velocity of gamma may lie anywhere in E.
Relative interval derivatives cover non-isolated endpoints; uniqueness excludes
invented velocities at isolated parameters. No density or completeness of D is
required, and there is no operator-norm continuity hypothesis. -/
theorem strong_operator_product_rule
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : Submodule ℝ E) (I : Set ℝ) (hI : Set.OrdConnected I)
    (K : ℝ → E →L[ℝ] F)
    (hK : ∀ v : E, ContinuousOn (fun t => K t v) I)
    (hKd : ∀ v : D, ∀ t ∈ I, DifferentiableWithinAt ℝ (fun s => K s (v : E)) I t)
    (gamma gammaVelocity : ℝ → E)
    (hgammaDomain : ∀ t ∈ I, gamma t ∈ D)
    (hgamma : ∀ t ∈ I, HasDerivWithinAt gamma (gammaVelocity t) I t) :
    ∀ t ∈ I, UniqueDiffWithinAt ℝ I t →
      HasDerivWithinAt (fun s => K s (gamma s))
        (derivWithin (fun s => K s (gamma t)) I t + K t (gammaVelocity t)) I t := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P23

end
