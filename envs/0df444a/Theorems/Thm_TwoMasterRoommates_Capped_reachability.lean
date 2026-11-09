-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_reachability
-- name    : TwoMasterRoommates.Capped.reachability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:59:31.251875+00:00
-- url     : https://prove2.me/theorems/469b6347-7a2f-4e9a-89d8-d6a1eb233b9f
-- title:
--   §1.1 and Appendix B — exact batch-graph reachability
-- statement:
--   Let $I$ be a two-master instance on an even positive number $n$ of identities whose integer master ranks are dense. Use the explicit alternating batch graph defined by §§B.2–B.7: its initial state has both cuts $-1$, no donors, and empty records and deletions; accepting states have both cuts maximal and no remaining obligations. Then
--
--   $$\exists M\,\operatorname{IsSolution}(I,M)\quad\Longleftrightarrow\quad\exists s\,\bigl(\operatorname{Accepting}(I,s)\ \text{and}\ \operatorname{init}(I)\longrightarrow^{*}_{\mathrm{BatchArc}(I)}s\bigr).$$
--
--   Arcs include every shape, cap, ownership and pair test, as well as existence of a marked-kernel solution with the exact cap (10). The retained opposite own-active guard survives into the following batch and inherited mandatory tokens must all be consumed there. Reachability is reflexive transitive closure of this explicit arc relation, independently of global matching feasibility. The empty and odd cases belong to the algorithmic goal separately.
--
--   Differences from the source:
--   - encoding: finite identity populations with arbitrary personal caps → finite labelled types, fixed-point-free involutions, and WithTop upper caps; reason: labels do not restrict populations; top is an infinite cap and every blocking comparison remains original and strict
--   - encoding: the explicit batch graph with physical cuts and record names → orientation-local cuts and records, exchanged once per handoff, with canonical unordered edge representatives; reason: this is a bijective relabelling of printed states; both orientations use the same tests
--   - reading: a genuinely new B target for Z′ and an already actual edge must remain literal → a new edge uses free endpoints, while an unchanged input edge of the prescribed Z′ shape may be retained; reason: the adjoining sentence explicitly retains existing actual edges ending at the terminal boundary
--   - reading: "an instance is feasible" for the batch graph of Appendix B → hypotheses 0 < n, Even n and Dense I (integer masters with dense tier ranks); reason: the graph is described only after the Appendix B preprocessing (p. 12: ranks compressed to tier indices, the empty instance accepted directly, odd sizes rejected); cap_compression transfers the statement to every instance
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 1 (PDF p. 2), reachability paragraph after Theorem 1.1; pp. 13–18 (PDF pp. 14–19), §§B.2–B.7

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Batch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

/-- The introduction's reachability characterization for the explicit Appendix B graph. -/
theorem reachability {n : ℕ} (hn : 0 < n) (heven : Even n)
    (I : Instance ℤ n) (hd : Dense I) :
    (∃ M, IsSolution I M) ↔
      ∃ s, Accepting I s ∧ Relation.ReflTransGen (BatchArc I) (init I) s := by sorry

end TwoMasterRoommates.Capped
