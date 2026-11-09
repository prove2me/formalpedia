-- Prove2me | Theorems.Thm_PulseSyncLowerBound_Pulse_lemma_11
-- name    : PulseSyncLowerBound.Pulse.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:23.335987+00:00
-- url     : https://prove2.me/theorems/c984f0b1-0f80-411b-9d00-25d6b0ce9b57
-- title:
--   Lemma 11 — cocycles are gradients
-- statement:
--   Let $X$ be any finite abstract simplicial complex that is path connected and whose every edge loop contracts by repeated-vertex and triangle moves and their inverses. If $\omega$ is an integer edge cocycle of $X$, then there exists an integer vertex potential $\vartheta$ such that
--
--   $$\omega(u,v)=\vartheta(v)-\vartheta(u)\qquad\text{for every }\{u,v\}\in X.$$
--
--   Both the triangle hypothesis and this conclusion include repeated-vertex faces. This is the source's general cocycle-to-gradient result, independent of any distributed protocol.
--
--   Differences from the source:
--   - encoding: cocycles and potentials on V(X) → functions on an ambient type with constraints only on actual faces; reason: off-vertex values are irrelevant and extend arbitrarily; the actual complex remains finite and closed under nonempty subsets
-- source:
--   Joel Rybicki, STOC 2027 submission #508 (October 2026), pinned published-basis artifact; Lemma 11; PDF p.17 / printed p.15; papers/stoc2027-508/source.pdf; SHA-256 5237f877941c17d0913977954f4f4b6ccba70f65ceae5dc47f15029dbd68765f.

import Definitions.Def_PulseSyncLowerBound_Pulse_Topology

namespace PulseSyncLowerBound.Pulse

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_11 {V : Type} (X : Set (Finset V)) (hX : IsFiniteComplex X)
    (hconn : EdgeSimplyConnected X) (ω : V → V → ℤ) (hω : EdgeCocycle X ω) :
    EdgeGradient X ω := by sorry

end PulseSyncLowerBound.Pulse
