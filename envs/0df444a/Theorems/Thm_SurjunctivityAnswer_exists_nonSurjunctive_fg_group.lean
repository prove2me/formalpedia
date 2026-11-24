-- Prove2me | Theorems.Thm_SurjunctivityAnswer_exists_nonSurjunctive_fg_group
-- name    : SurjunctivityAnswer.exists_nonSurjunctive_fg_group
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:53:55.389212+00:00
-- url     : https://prove2.me/theorems/921e729e-9b55-4e74-b164-0b11d5fc5590
-- title:
--   A finitely generated non-surjunctive group exists
-- statement:
--   There exists a **finitely generated** group $G$ that is not surjunctive:
--   $$ \exists\,G\ \text{finitely generated},\quad \neg\,\mathrm{IsSurjunctive}(G). $$
--
--   This is the goal of the mission strengthened by a finiteness condition on the witness, matching the source: the group carrying the counterexample is finitely generated. It records that the failure of surjunctivity is not confined to groups that are large in a generating-set sense.
--
--   **Formalization Note** `Group.FG G` is Mathlib's finite-generation predicate for groups. The witness comes from `OAI.OddKaplansky.main_theorem`, whose group is finitely generated and contains a nontrivial element of finite order; neither the torsion nor the characteristic is asserted here.
-- source:
--   OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic*, 26 September 2026, §8 (p. 23), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf; E. W. Weisstein, *Gottschalk Surjunctivity Conjecture*, MathWorld (derivation for $T_d$: finite support gives continuity, $ab=1$ gives equivariance and injectivity, $ba\neq1$ gives non-surjectivity), https://mathworld.wolfram.com/GottschalkSurjunctivityConjecture.html; OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, 23 September 2026, Section 7 (Lemma 7.1, Proposition 7.2, Corollary 7.3), https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_OddKaplansky
import Theorems.Thm_OAI_OddKaplansky_main_theorem

namespace SurjunctivityAnswer

theorem exists_nonSurjunctive_fg_group :
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      ¬ GottschalkSurjunctivity.IsSurjunctive G := by sorry

end SurjunctivityAnswer
