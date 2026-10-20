-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_lemma4
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.lemma4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:26:03.772798+00:00
-- url     : https://prove2.me/theorems/ec39e85c-aafe-493c-a62c-b1a73ea3d8ba
-- title:
--   Achievability of the cq Slepian–Wolf point
-- statement:
--   For a finite classical–quantum source $XQ$ with ensemble $E$, use iid copies, noiseless one-way communication from Alice to Bob, free private randomness and local operations, and no initial shared randomness. Achievability means that for every positive error and entropy tolerance, every sufficiently large positive blocklength admits keys with that disagreement bound, a uniformly exponentially bounded key alphabet, and the required Shannon entropy rate. Then
--
--   $$(C,R)=(H(X),H(X|Q))\quad\text{is achievable}.$$
--
--   All entropies are in bits. This is the source-coding rate point used in the common-randomness achievability argument.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 9, Lemma 4: the cq Slepian–Wolf rate point

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

/-- PDF p.9, Lemma 4: the cq Slepian--Wolf point is achievable in the paper's CR sense. -/
theorem lemma4 (E : CQData X Q) (hE : E.Valid) :
    CRAchievable (cqDensity E) (shannon E.prob) (classicalGivenQuantum E) := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
