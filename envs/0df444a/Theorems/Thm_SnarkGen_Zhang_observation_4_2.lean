-- Prove2me | Theorems.Thm_SnarkGen_Zhang_observation_4_2
-- name    : SnarkGen.Zhang.observation_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:11.279695+00:00
-- url     : https://prove2.me/theorems/207c63d3-0c2e-4a49-88c2-d413f75feeb9
-- title:
--   Observation 4.2 — Conjecture 4.1 is false: a cyclically 5-edge-connected permutation snark other than the Petersen graph
-- statement:
--   **Observation 4.2 (first sentence).** Conjecture 4.1 is false.
--
--   Zhang's Conjecture 4.1 asserts that every cubic, cyclically $5$-edge connected permutation graph that is a snark is isomorphic to the Petersen graph $P$. The statement is its negation:
--   $$
--   \neg\Big(\forall H \text{ finite}:\ H \text{ cubic} \wedge H \text{ cyclically 5-edge connected} \wedge H \text{ permutation graph} \wedge H \text{ snark} \Rightarrow H \cong P\Big).
--   $$
--   That is, there exists a finite cubic, cyclically $5$-edge connected permutation snark that is not isomorphic to the Petersen graph. The paper exhibits twelve such graphs on $34$ vertices in Appendix 8.6.
--
--   Observation 4.2 continues: "The smallest counterexamples have 34 vertices, and there are exactly 12 counterexamples of that order." Those two claims rest on an exhaustive computer enumeration and are **not** part of this statement; only the refutation is formalized.
--
--   **Formalization Note** The conjecture quantifies over finite vertex types in `Type` and reads "must be the Petersen graph" as the existence of a graph isomorphism to the Petersen graph on `Fin 10`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 9, Observation 4.2 (first sentence)

import Mathlib
import Definitions.Def_SnarkGen_Zhang_ZhangConjecture

namespace SnarkGen.Zhang

theorem observation_4_2 : ¬ ZhangConjecture := by sorry

end SnarkGen.Zhang
