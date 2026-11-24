-- Prove2me | Theorems.Thm_SurjunctivityAnswer_cellular_continuous
-- name    : SurjunctivityAnswer.cellular_continuous
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:51:36.108063+00:00
-- url     : https://prove2.me/theorems/42668894-5544-4f6f-8c52-ae4d86bdef3f
-- title:
--   Convolution maps are continuous
-- statement:
--   Let $K$ be a field equipped with a topology, assumed **discrete**, let $G$ be a group, and let $d\in K[G]$ have finite support. Give $K^{G}$ the product topology. Then the convolution map
--   $$ (T_d x)(g)\;=\;\sum_{u\in\operatorname{supp} d} d_u\,x(gu) $$
--   is continuous as a map $K^{G}\to K^{G}$.
--
--   Continuity is one of the two hypotheses in the topological formulation of surjunctivity, so this lemma is what makes an algebraically defined map admissible in that formulation. Together with shift-equivariance it also gives, via the Curtis–Hedlund–Lyndon theorem, the finite-memory description.
--
--   **Formalization Note** The topology on $K$ is an explicit instance binder, not a canonical choice: any discrete topology on $K$ is allowed, and the statement is universe-$0$ in both $K$ and $G$.
-- source:
--   OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic*, 26 September 2026, §8 (p. 23), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf; E. W. Weisstein, *Gottschalk Surjunctivity Conjecture*, MathWorld (derivation for $T_d$: finite support gives continuity, $ab=1$ gives equivariance and injectivity, $ba\neq1$ gives non-surjectivity), https://mathworld.wolfram.com/GottschalkSurjunctivityConjecture.html; OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, 23 September 2026, Section 7 (Lemma 7.1, Proposition 7.2, Corollary 7.3), https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_OddKaplansky

namespace SurjunctivityAnswer

theorem cellular_continuous (K G : Type) [Field K] [Group G] [TopologicalSpace K]
    [DiscreteTopology K] (d : MonoidAlgebra K G) :
    Continuous (OAI.OddKaplansky.cellular d) := by sorry

end SurjunctivityAnswer
