-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_presentation_transfer_with_advice_iff_total_search_selectors
-- name    : StudentTeacher976.Adaptivity.presentation_transfer_with_advice_iff_total_search_selectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:31:04.570554+00:00
-- url     : https://prove2.me/theorems/1c2dd24f-39eb-4b35-b084-5a0637436f1e
-- title:
--   Presentation transfer with advice is equivalent to total-search advice selectors
-- statement:
--   Fix a hierarchy level $i$ and admissible round and query functions $r,q$. A faithful refutation presentation specifies an underlying total search relation by a bounded universally quantified predicate. A uniform student uses one polynomial-time $\Sigma_i^p$-oracle program. An advised student additionally has one polynomially bounded advice string for each length of its encoded input, shared by all inputs of that length; the advice need not be computable.
--
--   The following two conditions are equivalent:
--
--   1. For every total search relation $R$ and every two faithful presentations $P,Q$ of $R$, existence of a uniform winning student for $Q$ within $(r,q)$ implies existence of an advised winning student for $P$ within the same budget.
--   2. Every total, polynomially bounded search relation with a $\Delta_{i+1}^p$ verifier has an $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$ selector.
--
--   Writing $W_{r,q}(Q)$ and $W_{r,q}^{\mathrm{adv}}(P)$ for the two kinds of solvability, the equivalence is
--
--   $$
--   \bigl[\forall R\,\forall P,Q\text{ presenting }R,\quad
--   W_{r,q}(Q)\Rightarrow W_{r,q}^{\mathrm{adv}}(P)\bigr]
--   \quad\Longleftrightarrow\quad
--   \mathrm{TFNP}^{\Sigma_i^p}\subseteq\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}.
--   $$
--
--   The criterion concerns unrestricted transfer across all presentations at one fixed admissible budget. It identifies the precise total-search assumption for such transfer even when the new student is allowed polynomial advice. It does not assert that the selector condition holds, or that this unrestricted transfer is necessary for any particular pair of presentations.
-- source:
--   Derived nonuniform interface criterion for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definitions 1.1–1.2, pp.6–7, admissible budgets of Theorem 1.4, p.7, and length-uniform advice as in the proof of Theorem 1.4, pp.20–21. This equivalence is a proved formalization consequence, not a separately numbered source assertion.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity
open AdviceComputations (InFPAdvice)

theorem StudentTeacher976.Adaptivity.presentation_transfer_with_advice_iff_total_search_selectors (i : ℕ) (r q : ℕ → ℕ)
    (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    (∀ (R : SearchRelation) (P Q : RefutablePresentation i R),
      (∃ g : Student,UniformStudent i g ∧ StudentShape Q r q g ∧ StudentWins Q r q g) →
      ∃ f : Student,
        (∃ F : Word → Word,InFPAdvice i F ∧ ∀ (x : Word) (t : ℕ) (H : List (List Word)),
          F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup (f x t H)) ∧
        StudentShape P r q f ∧ StudentWins P r q f) ↔
      AdviceSelectorTranslation.SelectorCollapse i := by sorry
