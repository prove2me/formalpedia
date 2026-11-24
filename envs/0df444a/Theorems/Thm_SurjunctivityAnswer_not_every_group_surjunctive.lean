-- Prove2me | Theorems.Thm_SurjunctivityAnswer_not_every_group_surjunctive
-- name    : SurjunctivityAnswer.not_every_group_surjunctive
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:54:25.400669+00:00
-- url     : https://prove2.me/theorems/198245a3-14fe-4497-b73a-6d091c6b52f8
-- title:
--   Not every group is surjunctive (negative answer to Gottschalk's question)
-- statement:
--   **Gottschalk's question has a negative answer.** There exists a group that is not surjunctive:
--   $$ \exists\,G\ \text{a group},\quad \neg\,\mathrm{IsSurjunctive}(G), $$
--   that is, there is a group $G$, a finite nonempty alphabet $A$, and an injective cellular automaton $A^{G}\to A^{G}$ that is not surjective.
--
--   Gottschalk asked in 1973 whether every group is surjunctive; the statement above is the negation of that assertion, in existence form. It is the weakest stable formulation of the answer: no characteristic, field size, presentation or generating-set condition is fixed, so the theorem is not invalidated by later, sharper counterexamples. As a positive theorem it can be imported as a lemma by any subsequent development, which a refuted universal statement cannot.
--
--   **Formalization Note** `GottschalkSurjunctivity.IsSurjunctive` is the published predicate: for every finite nonempty type $A$ with a discrete topology, every continuous, shift-equivariant, injective self-map of $A^{G}$ (product topology) is surjective. The witness is obtained from the proved platform theorem `OAI.OddKaplansky.main_theorem`; the corresponding universal statement `GottschalkSurjunctivity.gottschalk_surjunctivity_conjecture` carries an accepted disproof on the platform.
-- source:
--   OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic*, 26 September 2026, §8 (p. 23), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf; E. W. Weisstein, *Gottschalk Surjunctivity Conjecture*, MathWorld (derivation for $T_d$: finite support gives continuity, $ab=1$ gives equivariance and injectivity, $ba\neq1$ gives non-surjectivity), https://mathworld.wolfram.com/GottschalkSurjunctivityConjecture.html; W. H. Gottschalk, *Some general dynamical notions*, LNM 318 (1973), pp. 120-125, https://doi.org/10.1007/BFb0061728; OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, 23 September 2026, Section 7 (Lemma 7.1, Proposition 7.2, Corollary 7.3), https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_OddKaplansky
import Theorems.Thm_OAI_OddKaplansky_main_theorem

namespace SurjunctivityAnswer

theorem not_every_group_surjunctive :
    ∃ (G : Type) (_ : Group G), ¬ GottschalkSurjunctivity.IsSurjunctive G := by sorry

end SurjunctivityAnswer
