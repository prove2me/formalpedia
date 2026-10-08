-- Prove2me | Theorems.Thm_ProjSchedTW_DelayingModes_minimal_delaying_alternative_is_minimal_hitting_set
-- name    : ProjSchedTW.DelayingModes.minimal_delaying_alternative_is_minimal_hitting_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T22:40:52.658683+00:00
-- url     : https://prove2.me/theorems/28abc7f1-0e53-42b7-81f8-d57bf9c89c1f
-- title:
--   Lemma 2.5.5 — a minimal delaying alternative is a minimal set meeting every minimal forbidden subset
-- statement:
--   Let $F$ be a forbidden set and $B$ a minimal delaying alternative for $F$. Then $B$ is an inclusion-minimal set containing at least one activity of each minimal forbidden set $F'\subseteq F$:
--   $$B\cap F'\ne\emptyset\ \text{ for every minimal forbidden } F'\subseteq F,$$
--   and no proper subset of $B$ has this property.
--
--   The lemma links minimal forbidden sets and minimal delaying alternatives: a time-feasible strict order that makes some activity $i\in F\setminus B$ precede every activity of $B$ breaks up $F$. It is the combinatorial step of the proof of Theorem 2.5.7.
--
--   **Formalization Note.** Minimality is Mathlib's `Minimal` over all finite sets of activities. The standing assumptions of the model are hypotheses.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 49, Lemma 2.5.5

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

namespace ProjSchedTW.DelayingModes

theorem minimal_delaying_alternative_is_minimal_hitting_set {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (F B : Finset (Fin (n + 2)))
    (hF : P.IsForbidden F) (hB : P.IsMinimalDelayingAlternative F B) :
    Minimal (fun H : Finset (Fin (n + 2)) =>
      ∀ F' ⊆ F, P.IsMinimalForbidden F' → (H ∩ F').Nonempty) B := by sorry

end ProjSchedTW.DelayingModes
