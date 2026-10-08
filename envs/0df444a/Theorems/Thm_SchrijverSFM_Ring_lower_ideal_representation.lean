-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_lower_ideal_representation
-- name    : SchrijverSFM.Ring.lower_ideal_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:56.898977+00:00
-- url     : https://prove2.me/theorems/fd588194-843a-4b8f-9cdf-3e795bc24bd1
-- title:
--   §6, p. 353 — 𝒞 is the collection of all lower ideals of some partial order on V
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a ring family of subsets of $V$ (closed under union and intersection) with $\emptyset \in \mathcal C$ and $V \in \mathcal C$. For $v \in V$ let $M_v$ be the smallest set of $\mathcal C$ containing $v$, and assume $M_u \ne M_v$ for all $u \ne v$. Then there is a partial order $\preceq$ on $V$ (reflexive, transitive, antisymmetric) whose lower ideals are exactly the sets of $\mathcal C$:
--   $$X \in \mathcal C \iff \bigl(\forall u, v \in V:\ u \preceq v,\ v \in X \implies u \in X\bigr) \qquad (X \subseteq V).$$
--
--   This is the representation Schrijver uses to describe a ring family completely by the sets $M_v$, after the normalization $M = \emptyset$, $V \in \mathcal C$, $M_u \ne M_v$.
--
--   **Formalization Note** The partial order is given as a relation `r : V → V → Prop` with its three axioms stated explicitly. The hypotheses are the paper's normalization "We can assume that $M = \emptyset$, $V \in \mathcal C$, and $M_u \ne M_v$ for all $u \ne v$", where $M = \emptyset$ (the smallest set of $\mathcal C$ is empty) is `∅ ∈ C`.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 353, §6, second paragraph

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem lower_ideal_representation {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) :
    ∃ r : V → V → Prop,
      (∀ v, r v v) ∧ (∀ u v w, r u v → r v w → r u w) ∧ (∀ u v, r u v → r v u → u = v) ∧
      ∀ X : Finset V, X ∈ C ↔ ∀ u v, r u v → v ∈ X → u ∈ X := by sorry

end SchrijverSFM.Ring
