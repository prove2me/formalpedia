-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_satisfying_extension_from_partial
-- name    : RandomCNFDeficiency.LowerBound.satisfying_extension_from_partial
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:28.322041+00:00
-- url     : https://prove2.me/theorems/76619bc5-2c87-4e4e-aa6f-7991960d0acd
-- title:
--   Extending a satisfying assignment using a disjoint partial assignment
-- statement:
--   Let $A\subseteq B$ be finite signed CNFs. Suppose a partial Boolean assignment $\rho$ satisfies every clause of $B\setminus A$ and leaves every variable in $N(A)$ unassigned. Then
--
--   $$\operatorname{SAT}(A)\ \Longrightarrow\ \operatorname{SAT}(B).$$
--
--   Here $\operatorname{SAT}$ means existence of a total satisfying Boolean assignment. This extension principle allows a local satisfying assignment and a disjoint partial assignment to coexist.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Lemma 3.5, assignment construction and its immediate extension consequence, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.satisfying_extension_from_partial {n : ℕ} (A B : CNF n) (hAB : A ⊆ B)
    (ρ : Fin n → Option Bool) (hρ : ∀ C ∈ B \ A, PartialSatisfies ρ C)
    (hn : ∀ i ∈ neighborhood A, ρ i=none) (ha : Satisfiable A) : Satisfiable B := by sorry
