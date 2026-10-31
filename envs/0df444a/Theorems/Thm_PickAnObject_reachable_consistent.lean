-- Prove2me | Theorems.Thm_PickAnObject_reachable_consistent
-- name    : PickAnObject.reachable_consistent
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:35.793982+00:00
-- url     : https://prove2.me/theorems/d1b7d0ba-0e11-4fc5-acf8-0e1d7b89dc17
-- title:
--   Every collective history of a pick-an-object mechanism is consistent with some preference profile
-- statement:
--   Let $S$ be a menu function. Every collective history $h^A$ that a pick-an-object mechanism with menu function $S$ can produce — starting from $h^{A-\varnothing}$, with every agent choosing an arbitrary element of each non-empty menu she is offered — is consistent with some preference profile: there is a profile $P$ such that, for every agent $a$, every menu $\Omega$ and choice $\omega$ recorded in $h^A_a$, and every $o\in\Omega$,
--   $$\omega\;R_a\;o .$$
--
--   The reason is the structure of menus: a menu never contains the agent's previous choices or objects absent from her previous menu. This rationalizability is what Lemma 1 uses to represent outcomes after arbitrary histories through the rule.
--
--   Differences from the source:
--   - encoding: "every collective history that results from any number of periods of a PAO mechanism" → histories reachable from $h^{A-\varnothing}$ by arbitrary choices from the offered menus (an inductive predicate, $h^{A-\varnothing}$ included); reason: the paper's set $H^A_{\mathbb S}$ of histories of $\mathbb S$, p.11; $h^{A-\varnothing}$ is trivially consistent
--   - encoding: strict preferences over $O$ → rankings $O\simeq\{0,\dots,|O|-1\}$ with $\varnothing$ as `none`; reason: Lean convention; every strict linear order arises exactly once
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, §3, p.11, sentence after the definition of the PAO mechanism ("every collective history that results from any number of periods of a PAO mechanism is consistent with a non-empty set of preference profiles")

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **Every collective history of a pick-an-object mechanism is rationalizable**,
Bó–Hakimov, arXiv:2012.01025v4, §3, p.11: "Notice that because the menus given to each agent do
not include her previous choices and never include objects that were not present in previous
menus, every collective history that results from any number of periods of a PAO mechanism is
consistent with a non-empty set of preference profiles."

For every menu function `S` and every collective history `h` reachable in `S` (from
`h^{A−∅}`, under arbitrary choices from the menus offered), some preference profile is consistent
with `h`.

**Formalization Note.** Reachable histories include `h^{A−∅}` (trivially rationalizable). -/
theorem reachable_consistent {A Obj : Type*} [Fintype Obj] [DecidableEq Obj]
    (S : MenuFunction A Obj) (hS : IsMenuFunction S) (h : CollectiveHistory A Obj)
    (hh : Reachable S h) :
    ∃ P : Profile A Obj, ProfileConsistentWith P h := by sorry

end PickAnObject
