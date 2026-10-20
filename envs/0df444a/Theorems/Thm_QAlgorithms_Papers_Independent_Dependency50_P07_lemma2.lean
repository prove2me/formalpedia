-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_lemma2
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.lemma2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:23:43.395002+00:00
-- url     : https://prove2.me/theorems/1d6a8762-5c43-49ba-97eb-80b05db54db0
-- title:
--   Monotonicity and concavity of both cq curves
-- statement:
--   For a finite classical–quantum ensemble $E$, let $D^*(R)$ maximize $I(U;Q)$ over stochastic auxiliaries satisfying $I(U;X)-I(U;Q)\le R$, and set $C^*(R)=R+D^*(R)$. Both functions are nondecreasing on $[0,\infty)$. For $F=D^*$ and for $F=C^*$, every $R_1,R_2\ge0$ and $0\le\lambda\le1$ satisfy
--
--   $$\lambda F(R_1)+(1-\lambda)F(R_2)\le F(\lambda R_1+(1-\lambda)R_2).$$
--
--   These properties express the monotone trade-off and the ability to share rates between auxiliary channels.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 6, Lemma 2: monotonicity and concavity of the cq trade-off

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF pp.6--7, Lemma 2: both curves are nondecreasing and concave on the nonnegative half-line. -/
theorem lemma2 (E : CQData X Q) (hE : E.Valid) :
    MonotoneOn (dStar E) (Set.Ici 0) ∧ MonotoneOn (cStar E) (Set.Ici 0) ∧
    (∀ R1 R2 l : ℝ, 0 ≤ R1 → 0 ≤ R2 → 0 ≤ l → l ≤ 1 →
      l * dStar E R1 + (1-l) * dStar E R2 ≤ dStar E (l*R1+(1-l)*R2)) ∧
    (∀ R1 R2 l : ℝ, 0 ≤ R1 → 0 ≤ R2 → 0 ≤ l → l ≤ 1 →
      l * cStar E R1 + (1-l) * cStar E R2 ≤ cStar E (l*R1+(1-l)*R2)) := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
