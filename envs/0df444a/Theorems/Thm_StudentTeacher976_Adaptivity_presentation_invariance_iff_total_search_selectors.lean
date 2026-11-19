-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_presentation_invariance_iff_total_search_selectors
-- name    : StudentTeacher976.Adaptivity.presentation_invariance_iff_total_search_selectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:24:35.724478+00:00
-- url     : https://prove2.me/theorems/030ecc4c-4e62-4fdf-8c1c-92d5ed750ecb
-- title:
--   Presentation invariance is equivalent to total-search selectors
-- statement:
--   Fix a hierarchy level $i$ and admissible round and query functions $r,q$, with the conventions of Theorem 1.4. A faithful refutation presentation specifies an underlying total search relation $R$ by a bounded universally quantified refutation predicate. For a fixed presentation, solvability means that one uniform $\mathrm{FP}^{\Sigma_i^p}$ student satisfies the shape and winning conditions of Definition 1.2.
--
--   The following two conditions are equivalent:
--
--   1. For every total search relation $R$ and every two faithful presentations $P,Q$ of $R$, solvability using $Q$ within the budget $(r,q)$ implies solvability using $P$ within the same budget.
--   2. Every total, polynomially bounded search relation with a $\Delta_{i+1}^p$ verifier has a uniform $\mathrm{FP}^{\Sigma_i^p}$ selector.
--
--   In symbols, writing $\operatorname{Win}_{r,q}(P)$ for solvability with the fixed presentation $P$,
--
--   $$
--   \bigl[\forall R\,\forall P,Q\text{ presenting }R,\quad
--   \operatorname{Win}_{r,q}(Q)\Rightarrow\operatorname{Win}_{r,q}(P)\bigr]
--   \quad\Longleftrightarrow\quad
--   \mathrm{TFNP}^{\Sigma_i^p}\subseteq\mathrm{FP}^{\Sigma_i^p}.
--   $$
--
--   This criterion identifies exactly the extra search assumption required for unrestricted presentation invariance at any one admissible resource budget. It does not assume a decision-class hardness condition or assert that the selector condition holds.
-- source:
--   Derived interface criterion for Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definitions 1.1–1.2, pp.6–7, with the admissible budgets of Theorem 1.4, p.7. This equivalence is a proved formalization consequence, not a separately numbered assertion in the source.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_Selectors
set_option autoImplicit false

theorem StudentTeacher976.Adaptivity.presentation_invariance_iff_total_search_selectors (i : ℕ) (r q : ℕ → ℕ)
    (hr : StudentTeacher976.Adaptivity.AdmissibleRounds r)
    (hq : StudentTeacher976.Adaptivity.AdmissibleQueries q) :
    (∀ (R : StudentTeacher976.Adaptivity.SearchRelation)
      (P Q : StudentTeacher976.Adaptivity.RefutablePresentation i R),
      (∃ g : StudentTeacher976.Adaptivity.Student,
        StudentTeacher976.Adaptivity.UniformStudent i g ∧
        StudentTeacher976.Adaptivity.StudentShape Q r q g ∧
        StudentTeacher976.Adaptivity.StudentWins Q r q g) →
      ∃ f : StudentTeacher976.Adaptivity.Student,
        StudentTeacher976.Adaptivity.UniformStudent i f ∧
        StudentTeacher976.Adaptivity.StudentShape P r q f ∧
        StudentTeacher976.Adaptivity.StudentWins P r q f) ↔
      StudentTeacher976.Adaptivity.SelectorPresentationTranslation.SelectorCollapse i := by sorry
