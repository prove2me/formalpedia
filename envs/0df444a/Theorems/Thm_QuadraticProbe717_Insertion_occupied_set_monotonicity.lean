-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_occupied_set_monotonicity
-- name    : QuadraticProbe717.Insertion.occupied_set_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:04.515931+00:00
-- url     : https://prove2.me/theorems/f5cb55fe-2928-4611-85eb-3972a693a04d
-- title:
--   Lemma 2.4 — occupied-set monotonicity
-- statement:
--   Let $A\subseteq B$ be occupied sets. Fix a list of future insertions, each specified by its probe list, and use that same list in both tables. For every prefix length $t$,
--   $$\operatorname{runFrom}(A,t)\subseteq\operatorname{runFrom}(B,t).$$
--   Exhausted probe lists leave a table unchanged. Prefix lengths beyond the list length mean the whole list. This supplies the deterministic monotonicity statement without assumptions about a random law.
--
--   Differences from the source:
--   - generalization: occupied sets of a hash table with a common suffix of probe sequences → finite occupied sets in any carrier with decidable equality and arbitrary finite probe lists; reason: every complete finite-table probe sequence is an instance; exhausted lists are also allowed and preserve inclusion
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Lemma 2.4, p. 5 (PDF p. 5)

import Definitions.Def_QuadraticProbe717_Insertion_probing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem occupied_set_monotonicity {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : A ⊆ B) (sequences : List (List α)) (t : ℕ) :
    runFrom A sequences t ⊆ runFrom B sequences t := by sorry

end QuadraticProbe717.Insertion
