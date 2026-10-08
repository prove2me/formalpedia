-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_closure_union_inter
-- name    : SchrijverSFM.Ring.closure_union_inter
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:47.447767+00:00
-- url     : https://prove2.me/theorems/36fc5748-ba91-4309-a131-4ec68e6ca069
-- title:
--   §6, p. 354 (after (27)) — X̄ is the smallest set of 𝒞 containing X; X̄ ∪ Ȳ = (X ∪ Y)‾ and X̄ ∩ Ȳ ⊇ (X ∩ Y)‾
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a ring family on $V$ with $V \in \mathcal C$. For $X \subseteq V$ let $\overline X$ be the intersection of all sets of $\mathcal C$ containing $X$. Then:
--   1. for every $X \subseteq V$, $\overline X \in \mathcal C$, $X \subseteq \overline X$, and $\overline X \subseteq Y$ for every $Y \in \mathcal C$ with $X \subseteq Y$; that is, $\overline X$ is the smallest set in $\mathcal C$ containing $X$;
--   2. for all $X, Y \subseteq V$,
--   $$\overline X \cup \overline Y = \overline{X \cup Y} \qquad\text{and}\qquad \overline X \cap \overline Y \supseteq \overline{X \cap Y}.$$
--
--   These closure identities are the parenthetical remark that justifies the last two steps of display (27).
--
--   **Formalization Note** Item 1 is the defining property "the smallest set in $\mathcal C$ containing $X$" of p. 354, stated for the `Finset.inf` encoding of the closure; it needs $V \in \mathcal C$ so that some set of $\mathcal C$ contains $X$.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 354, §6, definition of X̄ before (26) and parenthetical remark after (27)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem closure_union_inter {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (huniv : Finset.univ ∈ C) :
    (∀ X : Finset V, closure C X ∈ C ∧ X ⊆ closure C X ∧
        ∀ Y ∈ C, X ⊆ Y → closure C X ⊆ Y) ∧
      ∀ X Y : Finset V, closure C X ∪ closure C Y = closure C (X ∪ Y) ∧
        closure C (X ∩ Y) ⊆ closure C X ∩ closure C Y := by sorry

end SchrijverSFM.Ring
