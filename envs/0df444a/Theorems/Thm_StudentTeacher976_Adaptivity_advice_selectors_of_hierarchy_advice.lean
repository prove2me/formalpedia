-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_advice_selectors_of_hierarchy_advice
-- name    : StudentTeacher976.Adaptivity.advice_selectors_of_hierarchy_advice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:15:44.098198+00:00
-- url     : https://prove2.me/theorems/0025cdeb-3db3-4763-96cb-311409bfbefc
-- title:
--   Hierarchy advice algorithms yield total-search advice selectors
-- statement:
--   Fix a hierarchy level $i\ge0$. Suppose that every language in $\Sigma_{i+1}^p$ is decidable in deterministic polynomial time with a fixed $\Sigma_i^p$ oracle and polynomial advice. Then every total, polynomially bounded search relation with a $\Delta_{i+1}^p$ verifier has a selector in $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$:
--
--   $$
--   \Sigma_{i+1}^p\subseteq\Delta_{i+1}^p/\mathrm{poly}
--   \quad\Longrightarrow\quad
--   \mathrm{TFNP}^{\Sigma_i^p}\subseteq\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}.
--   $$
--
--   More explicitly, let $T(x,y)$ be total, let its encoded graph belong to $\Delta_{i+1}^p$, and let one polynomial $b$ bound the length of every valid answer. There exist one polynomial-time $\Sigma_i^p$-oracle program and polynomially bounded length-uniform advice realizing a function $F$ such that $T(x,F(x))$ for every input word $x$, including the empty input. Advice is shared by all inputs of each length and need not be computable.
--
--   This nonuniform search-to-decision implication explains how a total verifiable search task without an advice selector supplies the decision-class hardness used in the mission. The polynomial advice model and oracle level are the published operational interfaces.
-- source:
--   Relativized nonuniform extension of Arora–Barak, Computational Complexity: A Modern Approach, January 2007 web draft, https://theory.cs.princeton.edu/complexity/book.pdf, §2.5 Decision versus search, Theorem 2.19, printed p.2.17 (55). Uses the bounded-witness prefix construction and length-uniform advice aggregation; the mission interfaces are Ježil–Tsintsilidas, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, §1.2.1 pp.6–7. The oracle/advice extension is stated explicitly here.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.advice_selectors_of_hierarchy_advice (i : ℕ) (hcontain : StudentTeacher976.Adaptivity.Sigma (i+1)⊆DeltaPoly i) :
    AdviceSelectorTranslation.SelectorCollapse i := by sorry
