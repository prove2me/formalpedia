-- Prove2me | Theorems.Thm_StableMatching_galeShapley_group_strategyproof_men
-- name    : StableMatching.galeShapley_group_strategyproof_men
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T13:43:10.156011+00:00
-- url     : https://prove2.me/theorems/4d2805b7-ec62-4c62-a1e8-ea9f7f233a4a
-- title:
--   Gale–Shapley is group strategy-proof for men
-- statement:
--   Let $C$ be a nonempty set of men and let $I'$ be obtained from $I$ by changing only the preference lists of the men in $C$. Let $\mu$ and $\mu'$ be the Gale–Shapley outcomes of $I$ and $I'$. Then it is not the case that every man $m \in C$ strictly prefers, according to his true list in $I$, $\mu'(m)$ to $\mu(m)$.
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

namespace StableMatching

theorem galeShapley_group_strategyproof_men {n : ℕ} (I I' : Instance n) (C : Finset (Fin n))
    (hC : C.Nonempty) (hdev : I.MenDeviation I' C) (μ μ' : Matching n)
    (hμ : I.IsGSOutcome μ) (hμ' : I'.IsGSOutcome μ') :
    ¬ ∀ m ∈ C, I.manPrefers m (μ' m) (μ m) := by sorry

end StableMatching
