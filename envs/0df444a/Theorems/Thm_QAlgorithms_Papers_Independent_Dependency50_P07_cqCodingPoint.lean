-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_cqCodingPoint
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.cqCodingPoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:29:43.430881+00:00
-- url     : https://prove2.me/theorems/5eea3cd0-b752-45c9-ac21-9531f3405809
-- title:
--   Achievability of the auxiliary-variable rate point
-- statement:
--   Let $XQ$ be a finite classical–quantum source and let $U$ be any finite stochastic auxiliary generated from $X$, so that $U\to X\to Q$. In the iid one-way common-randomness model, with free private randomness, no initial shared randomness, disagreement error and Shannon key entropy, the rate point
--
--   $$(C,R)=\bigl(I(U;X),\ I(U;X)-I(U;Q)\bigr)$$
--
--   is achievable. The common key alphabet has a single exponential blocklength bound. Zero mutual information and zero communication are included. This is the direct operational rate point underlying Theorem 1.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 11, §2, direct coding: the auxiliary-variable achievable point

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

/-- PDF p.11, direct coding: no positive-information or positive-communication exclusion. -/
theorem cqCodingPoint (E : CQData X Q) (hE : E.Valid) (V : Auxiliary X) :
    CRAchievable (cqDensity E) (auxIX E V) (auxCost E V) := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
