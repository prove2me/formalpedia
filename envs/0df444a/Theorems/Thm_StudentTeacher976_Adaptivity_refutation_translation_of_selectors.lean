-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_refutation_translation_of_selectors
-- name    : StudentTeacher976.Adaptivity.refutation_translation_of_selectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:24:21.019019+00:00
-- url     : https://prove2.me/theorems/dd416813-0f0a-42a6-a999-00b80eae3409
-- title:
--   Total-search selectors yield efficient refutation translations
-- statement:
--   Fix $i$ and assume that every total polynomially bounded search relation whose encoded graph lies in $\Delta_{i+1}^p$ has an $\mathrm{FP}^{\Sigma_i^p}$ selector. For any two refutable presentations $P,Q$ of the same total search relation, there exists an $\mathrm{FP}^{\Sigma_i^p}$ function $\psi$ on encoded triples such that, whenever $|z|=b_P(|x|)$,
--
--   $$
--   |\psi(x,y,z)|=b_Q(|x|),\qquad
--   Q(x,y,\psi(x,y,z))\Longrightarrow P(x,y,z).
--   $$
--
--   The tests $P$ and $Q$ in this formula are the presentations' success predicates. The selector hypothesis is an explicit additional assumption. The resulting map is an interface for transferring uniform students between presentations without increasing their resource budgets.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definition 1.2, p.7; selector-case refutation-translation interface developed for this formalization.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_Selectors
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.refutation_translation_of_selectors (i : ℕ) (hselectors : SelectorPresentationTranslation.SelectorCollapse i)
    (R : SearchRelation) (P Q : RefutablePresentation i R) :
    ∃ ψ : Word → Word → Word → Word,
      (∃ F : Word → Word,InFP i F ∧ ∀ x y z,F (tup [x,y,z])=ψ x y z) ∧
      (∀ x y z : Word,z.length=P.refutationLength.eval x.length →
        (ψ x y z).length=Q.refutationLength.eval x.length) ∧
      ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
        Q.test x y (ψ x y z) → P.test x y z := by sorry
