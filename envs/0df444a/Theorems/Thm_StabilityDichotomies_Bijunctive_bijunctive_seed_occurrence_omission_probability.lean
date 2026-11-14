-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_occurrence_omission_probability
-- name    : StabilityDichotomies.Bijunctive.bijunctive_seed_occurrence_omission_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:55:28.133956+00:00
-- url     : https://prove2.me/theorems/9155d03a-89a6-4954-a155-44886afe0a51
-- title:
--   An occurrence is omitted with probability ε/2 under the full seed law
-- statement:
--   Under the complete Definition 4.8 product seed law, for $0<\varepsilon\le1$, the probability that a fixed original constraint occurrence is omitted from the graph subinstance is exactly $\varepsilon/2$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definition 4.8 and proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_seed_occurrence_omission_probability {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin I.constraints.card) :
    (bijunctiveSeedMeasure rep I ε {seed | 1 - ε / 2 < seed.1 i}).toReal = ε / 2 := by
  sorry
