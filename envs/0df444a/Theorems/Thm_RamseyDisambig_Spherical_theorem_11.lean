-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_theorem_11
-- name    : RamseyDisambig.Spherical.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:35.005708+00:00
-- url     : https://prove2.me/theorems/0310d004-a0be-4466-8ddd-452786c9e5f9
-- title:
--   Theorem 11 — Pálvölgyi's Dense Block theorem
-- statement:
--   Let $G$ be any finite solvable group and let $X$ be any finite set on which $G$ acts. Then
--   $$\text{the action }G\curvearrowright X\text{ has the dense block property}.$$
--   Explicitly, for each positive number of colors $r$, positive input dimension $m$ and $0<\eta<1$, positive integers $n,k$ are uniform over all colorings $c:X^n\to\{0,\ldots,r-1\}$. They satisfy $mk\ge(1-\eta)n$, and each such coloring admits a block map whose induced coloring depends only on the orbit of each input coordinate.
--
--   No transitivity or nonemptiness of $X$ is assumed. This is the full external theorem cited by the source as [Pá26, Theorem 11], not merely its dihedral specialization. It is posed as a milestone requiring a proof, rather than assumed in Lemma 12 or in the goal.
--
--   Differences from the source:
--   - reading: r,m,n,k ∈ ℕ in the dense block property → r,m,n,k ≥ 1; reason: the positive-integer reading prevents zero-dimensional or zero-block witnesses from making the result vacuous; see paper.md, Recorded reading
--   - encoding: [r], finite groups and actions on finite sets → Fin r, Group.IsSolvable, Finite instances and MulAction; reason: these encode precisely the given groups, all finite action sets and their actions; inactive-coordinate letters preserve empty sets
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 11 and dense block definition, p. 11 (printed = PDF), citing Pálvölgyi 2026, Theorem 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_BlockMaps

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- Theorem 11, p. 11, cited there from Pálvölgyi 2026, Theorem 11.
No transitivity or nonemptiness of the action set is assumed. -/
theorem theorem_11 (G X : Type*) [Group G] [Finite G] [Group.IsSolvable G]
    [Finite X] [MulAction G X] : DenseBlockProperty G X := by sorry

end RamseyDisambig.Spherical
