-- Prove2me | Theorems.Thm_StudentTeacher976_Adaptivity_adaptivity_separation_of_total_search_selectors
-- name    : StudentTeacher976.Adaptivity.adaptivity_separation_of_total_search_selectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:31:27.295432+00:00
-- url     : https://prove2.me/theorems/a855a2a8-3da6-45cb-aca8-000b5ad17c0d
-- title:
--   Adaptivity separation assuming efficient total-search selectors
-- statement:
--   Fix a hierarchy level $i$, assume $\Sigma_{i+1}^p\not\subseteq\Delta_{i+1}^p/\mathrm{poly}$, and let $r,q$ satisfy exactly the source's admissibility conditions. Assume additionally that every total polynomially bounded search relation with a $\Delta_{i+1}^p$ verifier has a uniform $\mathrm{FP}^{\Sigma_i^p}$ selector. Then
--
--   $$
--   \mathrm{ST}^{\Sigma_i^p}[r+1,1]\not\subseteq\mathrm{ST}^{\Sigma_i^p}[r,q].
--   $$
--
--   This is the efficient-selector case of the semantic separation. Both ST classes quantify over faithful presentations of the underlying total search relation; no common presentation is assumed. The additional selector assumption is explicitly part of this supporting theorem, rather than a hypothesis of the mission's main theorem.
-- source:
--   Proof-case decomposition of Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, Theorem 1.4 p.7 and canonical construction §3.1 pp.19–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf. The explicit total-search case assumption is introduced by this formal development and is not an additional assumption of the source theorem.

import Definitions.Def_StudentTeacher976_Adaptivity_Game
import Definitions.Def_StudentTeacher976_Adaptivity_Selectors
open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity
theorem adaptivity_separation_of_total_search_selectors (i : ℕ)
    (hardness : ¬ Sigma (i+1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : SelectorPresentationTranslation.SelectorCollapse i) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q := by sorry
end StudentTeacher976.Adaptivity
