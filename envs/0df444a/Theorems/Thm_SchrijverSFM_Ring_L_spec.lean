-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_L_spec
-- name    : SchrijverSFM.Ring.L_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:57.147814+00:00
-- url     : https://prove2.me/theorems/453507f5-b717-40ee-9459-285d6a96b87b
-- title:
--   §6, p. 353 — L_v is the largest set in 𝒞 not containing v, the union of the M_u not containing v, and L_v ∪ {v} ∈ 𝒞
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a ring family on $V$ with $\emptyset, V \in \mathcal C$ and $M_u \ne M_v$ for $u \ne v$, where $M_v$ is the smallest set of $\mathcal C$ containing $v$. For $v \in V$ let $L_v$ be the union of all sets of $\mathcal C$ not containing $v$. Then:
--   1. $L_v \in \mathcal C$ and $v \notin L_v$;
--   2. every $Y \in \mathcal C$ with $v \notin Y$ satisfies $Y \subseteq L_v$, so $L_v$ is the largest set in $\mathcal C$ not containing $v$;
--   3. $L_v$ is the union of those $M_u$ not containing $v$:
--   $$L_v = \bigcup_{u \in V,\ v \notin M_u} M_u;$$
--   4. $L_v \cup \{v\} \in \mathcal C$.
--
--   Item 4 is what makes the weight $c(v) = \max\{0, f(L_v) - f(L_v \cup \{v\})\}$ of display (23) depend only on the values of $f$ on $\mathcal C$.
--
--   **Formalization Note** Items 1–3 are the parenthetical description of $L_v$ on p. 353; item 4 is implicit in (23), which evaluates $f$ at $L_v \cup \{v\}$, and it needs the hypothesis $M_u \ne M_v$.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 353, §6, sentence defining L_v and display (23)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem L_spec {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) (v : V) :
    L C v ∈ C ∧ v ∉ L C v ∧ (∀ Y ∈ C, v ∉ Y → Y ⊆ L C v) ∧
      L C v = (Finset.univ.filter (fun u => v ∉ M C u)).biUnion (fun u => M C u) ∧
      insert v (L C v) ∈ C := by sorry

end SchrijverSFM.Ring
