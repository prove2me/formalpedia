-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_lemma_4
-- name    : OrdinalMSP.Forbidden.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:37.86368+00:00
-- url     : https://prove2.me/theorems/3b755cce-b1e7-4ed7-aab9-228e8e2e85c4
-- title:
--   Lemma 4, p. 6 — OPT ∩ Q ⊆ OPT(Q)
-- statement:
--   Let $\mathcal M$ be a matroid on the finite ground set $R$, totally ordered by the value order $\succ$, and let $\mathrm{OPT}(Q)$ denote the greedy (lexicographically optimum) base of $Q \subseteq R$, with $\mathrm{OPT} = \mathrm{OPT}(R)$. Then for every $Q \subseteq R$,
--   $$\mathrm{OPT} \cap Q \subseteq \mathrm{OPT}(Q).$$
--
--   In words, the optimum improves every subset: an element of the global optimum that is present in $Q$ is also selected by the greedy algorithm run on $Q$ alone. In the proof of the Key Lemma this gives $r^* \in \mathrm{OPT}(R_t)$ for every $r^* \in \mathrm{OPT}$ arriving at time $t$, which is the hypothesis under which the $k$-forbidden property applies.
--
--   **Formalization Note** The matroid's ground set is assumed to be all of $R$; $\mathrm{OPT}(Q)$ is the span characterization of the greedy output from the Setting definition.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, Lemma 4, p. 6

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

namespace OrdinalMSP.Forbidden

theorem lemma_4 {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (Q : Finset R) :
    opt M Finset.univ ∩ Q ⊆ opt M Q := by sorry

end OrdinalMSP.Forbidden
