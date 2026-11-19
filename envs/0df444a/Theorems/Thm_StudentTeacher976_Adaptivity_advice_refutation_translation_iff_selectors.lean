-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_advice_refutation_translation_iff_selectors
-- name    : StudentTeacher976.Adaptivity.advice_refutation_translation_iff_selectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:05:54.20422+00:00
-- url     : https://prove2.me/theorems/5cc436cd-6d4a-43c9-a842-2491dfbda3df
-- title:
--   Advice refutation translation is equivalent to advice total-search selection
-- statement:
--   Fix a hierarchy level $i$. The following two statements are equivalent.
--
--   1. For every total bounded search relation $R$ and every pair of faithful refutable presentations $P,Q$ with $\Delta_{i+1}^p$ success tests, there is a function $\psi(x,y,z)$ in $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$ on encoded triples satisfying, for each reply of prescribed $P$-length,
--
--   $$
--   |\psi(x,y,z)|=b_Q(|x|),\qquad Q(x,y,\psi(x,y,z))\Longrightarrow P(x,y,z).
--   $$
--
--   2. Every total polynomially bounded search relation whose encoded graph belongs to $\Delta_{i+1}^p$ has a selector in $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$:
--
--   $$
--   \forall x\;T(x,f(x)).
--   $$
--
--   A map in the first statement may depend on both fixed presentations and on the proposed candidate. Each computation uses a fixed oracle program, and its polynomial advice is shared by all inputs of each encoded length. Zero certificate lengths are permitted.
--
--   This equivalence characterizes a general presentation-normalization principle. It does not assert either of the equivalent conditions, or that such a universal principle is necessary for a particular game separation.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Definition 1.2 p.7 and length-uniform advice condition in Theorem 1.4 p.7. Derived interface classification using the certified-replacement game; both implications formalized in this development.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity
open AdviceComputations (InFPAdvice)

theorem StudentTeacher976.Adaptivity.advice_refutation_translation_iff_selectors (i : ℕ) :
    (∀ (R : SearchRelation) (P Q : RefutablePresentation i R),
      ∃ ψ : Word → Word → Word → Word,
        (∃ F : Word → Word,InFPAdvice i F ∧ ∀ x y z,F (tup [x,y,z])=ψ x y z) ∧
        (∀ x y z : Word,z.length=P.refutationLength.eval x.length →
          (ψ x y z).length=Q.refutationLength.eval x.length) ∧
        ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
          Q.test x y (ψ x y z) → P.test x y z) ↔ AdviceSelectorTranslation.SelectorCollapse i := by sorry
