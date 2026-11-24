-- Prove2me | Theorems.Thm_SurjunctivityAnswer_cellular_isShiftEquivariant
-- name    : SurjunctivityAnswer.cellular_isShiftEquivariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:52:06.171803+00:00
-- url     : https://prove2.me/theorems/5b831b62-fb39-4300-b0ff-8a9d28d7340a
-- title:
--   Convolution maps commute with the left shift
-- statement:
--   Let $K$ be a field, $G$ a group and $d\in K[G]$ a finitely supported element. The **left shift** of a configuration $x:G\to K$ by $h\in G$ is $(h\cdot x)(g)=x(h^{-1}g)$. The convolution map $(T_d x)(g)=\sum_{u} d_u\,x(gu)$ satisfies
--   $$ T_d(h\cdot x)\;=\;h\cdot T_d(x)\qquad\text{for all } h\in G,\ x:G\to K .$$
--
--   Equivariance is the second hypothesis in the topological formulation of surjunctivity, and it expresses that right convolution is defined by the same rule at every cell. The statement holds for every field and every group, with no finiteness assumption on $K$.
--
--   **Formalization Note** The shift convention is the published one, `GottschalkSurjunctivity.shift`, namely $(h\cdot x)(g)=x(h^{-1}g)$; the convolution convention is `OAI.OddKaplansky.cellular`, which reads $x$ at $gu$ on the right.
-- source:
--   OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic*, 26 September 2026, §8 (p. 23), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf; E. W. Weisstein, *Gottschalk Surjunctivity Conjecture*, MathWorld (derivation for $T_d$: finite support gives continuity, $ab=1$ gives equivariance and injectivity, $ba\neq1$ gives non-surjectivity), https://mathworld.wolfram.com/GottschalkSurjunctivityConjecture.html; OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, 23 September 2026, Section 7 (Lemma 7.1, Proposition 7.2, Corollary 7.3), https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_OddKaplansky

namespace SurjunctivityAnswer

theorem cellular_isShiftEquivariant (K G : Type) [Field K] [Group G]
    (d : MonoidAlgebra K G) :
    GottschalkSurjunctivity.IsShiftEquivariant G (OAI.OddKaplansky.cellular d) := by sorry

end SurjunctivityAnswer
