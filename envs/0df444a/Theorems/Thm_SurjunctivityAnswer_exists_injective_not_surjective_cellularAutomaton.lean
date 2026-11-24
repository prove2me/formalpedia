-- Prove2me | Theorems.Thm_SurjunctivityAnswer_exists_injective_not_surjective_cellularAutomaton
-- name    : SurjunctivityAnswer.exists_injective_not_surjective_cellularAutomaton
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:53:21.847357+00:00
-- url     : https://prove2.me/theorems/54301a67-4a48-4914-99e2-93f8f164b55a
-- title:
--   An injective, non-surjective cellular automaton exists
-- statement:
--   There exist a group $G$, a finite nonempty alphabet $A$, and a cellular automaton $\tau:A^{G}\to A^{G}$ such that
--   $$ \tau\ \text{is injective}\quad\text{and}\quad \tau\ \text{is not surjective}. $$
--
--   This is the counterexample to Gottschalk's question stated purely in the language of symbolic dynamics: no group algebra, no characteristic and no field size appear in the statement. It isolates exactly the dynamical content of the 2026 construction, and it is the form in which later work on cellular automata can consume the refutation.
--
--   **Formalization Note** The witness is supplied by the proved platform theorem `OAI.OddKaplansky.main_theorem`, which provides a finite field $K$ of odd characteristic $p$ with $|K|=p^{4}$, a finitely generated group $G$ with nontrivial torsion, and $a,b\in K[G]$ with $ab=1\neq ba$ for which the convolution map of $b$ is injective and not surjective. The alphabet $A$ is that field, and the cellular-automaton property is the finite-memory statement about convolution.
-- source:
--   OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Odd Characteristic*, 26 September 2026, §8 (p. 23), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Odd-Characteristic-September-26-2026/paper.pdf; E. W. Weisstein, *Gottschalk Surjunctivity Conjecture*, MathWorld (derivation for $T_d$: finite support gives continuity, $ab=1$ gives equivariance and injectivity, $ba\neq1$ gives non-surjectivity), https://mathworld.wolfram.com/GottschalkSurjunctivityConjecture.html; OpenAI, *A Counterexample to Kaplansky's Direct-Finiteness Conjecture in Characteristic Two*, 23 September 2026, Section 7 (Lemma 7.1, Proposition 7.2, Corollary 7.3), https://github.com/openai/math/blob/main/preprints/A-Counterexample-to-Kaplanskys-Direct-Finiteness-Conjecture-in-Characteristic-Two-September-23-2026/paper.pdf

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_OddKaplansky
import Theorems.Thm_OAI_OddKaplansky_main_theorem

namespace SurjunctivityAnswer

theorem exists_injective_not_surjective_cellularAutomaton :
    ∃ (G : Type) (_ : Group G) (A : Type) (_ : Fintype A) (_ : Nonempty A)
      (τ : (G → A) → (G → A)),
      GottschalkSurjunctivity.IsCellularAutomaton G τ ∧
        Function.Injective τ ∧ ¬ Function.Surjective τ := by sorry

end SurjunctivityAnswer
