-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_adaptivity_separation_of_advice_total_search_selectors
-- name    : StudentTeacher976.Adaptivity.adaptivity_separation_of_advice_total_search_selectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:54:14.245282+00:00
-- url     : https://prove2.me/theorems/8cf6e984-92ec-4d7c-bf47-8dbcd75e5fd6
-- title:
--   Adaptivity separation assuming total-search selectors with polynomial advice
-- statement:
--   Let $i\ge0$, and suppose $\Sigma_{i+1}^p\not\subseteq\Delta_{i+1}^p/\mathrm{poly}$. Assume additionally that every total polynomially bounded search relation with a $\Delta_{i+1}^p$-decidable encoded graph has a selector in $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$. Advice is shared by every input of a given length and is polynomially bounded.
--
--   For every polynomial-time, nondecreasing, unbounded $r$ satisfying $1\le r(m)\le m^{1-\varepsilon}$ at positive lengths for some $\varepsilon>0$, and every positive polynomial-time, polynomially bounded query function $q$,
--
--   $$
--   \mathrm{ST}^{\Sigma_i^p}[r(m)+1,1]\not\subseteq\mathrm{ST}^{\Sigma_i^p}[r(m),q(m)].
--   $$
--
--   The conclusion concerns underlying relations and allows arbitrary faithful presentations. The selector assumption is an explicit additional hypothesis, weaker than requiring uniform selectors. This variant isolates a sufficient search-class condition for handling changes of presentation in the nonuniform lower-bound argument.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, Theorem 1.4, p.7; §3.1, pp.19–21 and Appendix A, pp.39–40. Variant with an explicit additional selector hypothesis and a strengthened advice-student lower bound.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem StudentTeacher976.Adaptivity.adaptivity_separation_of_advice_total_search_selectors
    (i : ℕ) (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i+1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : AdviceSelectorTranslation.SelectorCollapse i) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q := by sorry
