-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_2_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_2_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:40:24.640309+00:00
-- url     : https://prove2.me/theorems/5119aa52-8514-4d0f-b61d-ffe5aa0131f2
-- title:
--   Proposition 2.2
-- statement:
--   Let $e:[0,1]\to\mathbb R$ be continuous and convex. For real $r$, define the extended-real variational function
--
--   $$\psi(r)=-\sup_{0\le s<1}\frac{-sr-e(s)}{1-s}.$$
--
--   The function $\psi$ is concave and nondecreasing on $\mathbb R$, is finite and continuous for $r>-e(1)$, is upper semicontinuous on $\mathbb R$, and satisfies $\psi(-e(1))=e(1)-D_-e(1)$, allowing $D_-e(1)=+\infty$.
--
--   This formulation retains the infinite endpoint value without taking an inverse at infinity.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 7, Proposition 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2.2, all three clauses, arXiv:1109.3804v2, PDF p.7.
Psi is defined by (2.4), avoiding a fictitious real inverse at infinite slope. -/
theorem proposition_2_2 (e : ℝ → ℝ)
    (hcont : ContinuousOn e (Set.Icc (0 : ℝ) 1))
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) e) :
    (∀ r : ℝ, hoeffdingTransform e r =
      -sSup {v | ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ v = (((-s * r - e s) / (1 - s) : ℝ) : EReal)}) ∧
    (∀ r q u : ℝ, 0 ≤ u → u ≤ 1 →
      (u : EReal) * hoeffdingTransform e r + ((1 - u : ℝ) : EReal) * hoeffdingTransform e q ≤
        hoeffdingTransform e (u * r + (1 - u) * q)) ∧
    Monotone (hoeffdingTransform e) ∧
    (∀ r : ℝ, -e 1 < r → ∃ v : ℝ, hoeffdingTransform e r = (v : EReal)) ∧
    hoeffdingTransform e (-e 1) = (e 1 : EReal) - leftSlope 0 e 1 ∧
    ContinuousOn (hoeffdingTransform e) (Set.Ioi (-e 1)) ∧
    UpperSemicontinuous (hoeffdingTransform e) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
