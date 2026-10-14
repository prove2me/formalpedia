-- Prove2me | Theorems.Thm_StableMatching_galeShapley_truthful_men
-- name    : StableMatching.galeShapley_truthful_men
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:42:48.233099+00:00
-- url     : https://prove2.me/theorems/fb840d91-e3f5-4bfc-a1af-9ae154957657
-- title:
--   Gale–Shapley is truthful for men
-- statement:
--   Let $I'$ be obtained from $I$ by changing only the preference list of one man $m$. Let $\mu$ and $\mu'$ be the Gale–Shapley outcomes of $I$ and $I'$. Then $m$ does not strictly prefer, according to his true list in $I$, his partner $\mu'(m)$ to $\mu(m)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_truthful_men {n : ℕ} (I I' : Instance n) (m : Fin n)
    (hdev : I.MenDeviation I' {m}) (μ μ' : Matching n)
    (hμ : I.IsGSOutcome μ) (hμ' : I'.IsGSOutcome μ') :
    ¬ I.manPrefers m (μ' m) (μ m) := by sorry

end StableMatching
