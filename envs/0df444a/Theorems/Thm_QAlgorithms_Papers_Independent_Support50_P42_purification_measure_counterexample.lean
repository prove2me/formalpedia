-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_purification_measure_counterexample
-- name    : QAlgorithms.Papers.Independent.Support50.P42.purification_measure_counterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:27:04.55246+00:00
-- url     : https://prove2.me/theorems/cf3dc8ff-a7be-4334-a324-ec52aa8393ee
-- title:
--   Classical correlation defeats the purification-minimum prescription
-- statement:
--   Let $\chi=(|00\rangle\langle00|+|11\rangle\langle11|)/2$. Consider all normalized pure states on $AC:BD$ with arbitrary positive finite ancillary dimensions for $C,D$ whose partial trace over the ancillas is the displayed classically correlated two-qubit density. The set of their entropies across $AC:BD$ is nonempty and bounded below, but
--
--   $$\inf_{|\Phi\rangle:\ \operatorname{Tr}_{CD}|\Phi\rangle\langle\Phi|=\chi} S(\Phi_{BD})>0.$$
--
--   Nevertheless the two-qubit state is separable and an actual finite local protocol prepares it from a one-dimensional product input, without any singlets. This is the source's objection to this proposed measure, distinct from its operational formation definition.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 17, §V: classical correlation defeats the suggested purification minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.17: the purification-minimum prescription assigns positive value
to a classically correlated density obtainable by actual local preparation
from no shared entanglement. Both ancillary dimensions vary in the infimum. -/
theorem purification_measure_counterexample :
    (purificationScores classicalPair).Nonempty ∧ BddBelow (purificationScores classicalPair) ∧
    0<purificationMinimum classicalPair ∧ Entanglement.IsSeparablePositive classicalPair ∧
    ∃ L : Superop (Fin 1 × Fin 1) (Fin 2 × Fin 2),
      FiniteLOCC L ∧ L (1 : Op (Fin 1 × Fin 1))=classicalPair := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
