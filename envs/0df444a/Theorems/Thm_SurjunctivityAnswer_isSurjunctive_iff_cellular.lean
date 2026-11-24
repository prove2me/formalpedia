-- Prove2me | Theorems.Thm_SurjunctivityAnswer_isSurjunctive_iff_cellular
-- name    : SurjunctivityAnswer.isSurjunctive_iff_cellular
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:52:39.000119+00:00
-- url     : https://prove2.me/theorems/564fb7b8-d967-4e65-9bf8-6b2ac5fbba92
-- title:
--   Surjunctivity: cellular-automaton and continuous-equivariant formulations agree
-- statement:
--   For a group $G$ the following two statements are equivalent.
--
--   1. For every finite nonempty alphabet $A$ carrying a discrete topology, every map $\tau:A^{G}\to A^{G}$ that is continuous for the product topology, commutes with the left shift, and is injective, is surjective.
--   2. For every finite nonempty alphabet $A$, every cellular automaton $\tau:A^{G}\to A^{G}$ — that is, a map given by a finite memory set and a local rule — that is injective is surjective.
--
--   $$ \mathrm{IsSurjunctive}(G)\iff \big(\forall A,\ \forall \tau\in\mathrm{CA}(G,A),\ \tau\ \text{injective}\Rightarrow\tau\ \text{surjective}\big). $$
--
--   This identifies the topological formulation used in the formal development with Gottschalk's original formulation in terms of cellular automata, so that a witness produced in either language refutes or establishes the same property. It is a direct consequence of the Curtis–Hedlund–Lyndon characterisation.
--
--   **Formalization Note** The left-hand side is the published predicate `GottschalkSurjunctivity.IsSurjunctive`; the right-hand side uses `GottschalkSurjunctivity.IsCellularAutomaton`. Both quantifiers range over alphabets in universe $0$; the empty alphabet is excluded on both sides.
-- source:
--   T. Ceccherini-Silberstein, M. Coornaert, *Cellular Automata and Groups*, Springer 2010, https://doi.org/10.1007/978-3-642-14034-1, Section 1.8 (Curtis-Hedlund theorem) and Chapter 3 (surjunctive groups); W. H. Gottschalk, *Some general dynamical notions*, LNM 318 (1973), pp. 120-125, https://doi.org/10.1007/BFb0061728

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Theorems.Thm_GottschalkSurjunctivity_curtis_hedlund_lyndon

namespace SurjunctivityAnswer

theorem isSurjunctive_iff_cellular (G : Type) [Group G] :
    GottschalkSurjunctivity.IsSurjunctive G ↔
      ∀ (A : Type) [Fintype A] [Nonempty A] (τ : (G → A) → (G → A)),
        GottschalkSurjunctivity.IsCellularAutomaton G τ →
        Function.Injective τ → Function.Surjective τ := by sorry

end SurjunctivityAnswer
