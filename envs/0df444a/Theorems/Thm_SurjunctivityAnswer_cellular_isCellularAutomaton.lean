-- Prove2me | Theorems.Thm_SurjunctivityAnswer_cellular_isCellularAutomaton
-- name    : SurjunctivityAnswer.cellular_isCellularAutomaton
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:51:01.238727+00:00
-- url     : https://prove2.me/theorems/d4bfe7e4-61f0-42ea-b81a-3d633cbdaf10
-- title:
--   Right convolution is a cellular automaton
-- statement:
--   Let $K$ be a field, $G$ a group, and $d=\sum_{u\in G} d_u\,u$ an element of the group algebra $K[G]$, so that only finitely many coefficients $d_u$ are nonzero. The **convolution map** of $d$ acts on configurations $x:G\to K$ by
--   $$ (T_d x)(g)\;=\;\sum_{u\in\operatorname{supp} d} d_u\,x(gu),\qquad g\in G .$$
--   Then $T_d$ is a **cellular automaton** over $G$ with alphabet $K$: there exist a finite memory set $S\subseteq G$ and a local rule $\mu:K^{S}\to K$ such that
--   $$ (T_d x)(g)\;=\;\mu\big(s\mapsto x(gs)\big)\qquad\text{for all } x:G\to K,\ g\in G .$$
--
--   This is the step that turns a group-algebra element into an object of symbolic dynamics. It is what allows an algebraic failure of direct finiteness to be read as a statement about cellular automata, and it is reusable for any finitely supported coefficient function over any field.
--
--   **Formalization Note** The memory set is a `Finset G` and the local rule is a function on the subtype `S → K`, as required by the published predicate `GottschalkSurjunctivity.IsCellularAutomaton`. The map is `OAI.OddKaplansky.cellular`, taken as published. No topology occurs in this formulation, and $K$ is not required to be finite here.
-- source:
--   OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic*, 26 September 2026, §8 (p. 23), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf; E. W. Weisstein, *Gottschalk Surjunctivity Conjecture*, MathWorld (derivation for $T_d$: finite support gives continuity, $ab=1$ gives equivariance and injectivity, $ba\neq1$ gives non-surjectivity), https://mathworld.wolfram.com/GottschalkSurjunctivityConjecture.html; OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, 23 September 2026, Section 7 (Lemma 7.1, Proposition 7.2, Corollary 7.3), https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_OddKaplansky

namespace SurjunctivityAnswer

theorem cellular_isCellularAutomaton (K G : Type) [Field K] [Group G]
    (d : MonoidAlgebra K G) :
    GottschalkSurjunctivity.IsCellularAutomaton G (OAI.OddKaplansky.cellular d) := by sorry

end SurjunctivityAnswer
