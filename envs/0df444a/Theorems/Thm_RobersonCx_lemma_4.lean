-- Prove2me | Theorems.Thm_RobersonCx_lemma_4
-- name    : RobersonCx.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:27.281998+00:00
-- url     : https://prove2.me/theorems/4ec87019-bde8-478c-abd9-96ad6320ffe4
-- title:
--   Lemma 4 — an immersion of a cubic graph in a subcubic graph is a topological minor
-- statement:
--   Let $H$ be a cubic graph (every vertex has degree $3$) and $G$ a subcubic graph (maximum degree at most $3$). If $H$ immerses in $G$, then $G$ contains $H$ as a topological minor.
--
--   This transfers the minor exclusion of $B^{(r)}_q$ to immersion exclusion in Theorem 9.
--
--   Differences from the source:
--   - encoding: topological minor → the subdivision model `IsTopMinor`; reason: equivalent to a subgraph isomorphic to a subdivision
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 4, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_RobersonCx_IsImmersion
import Definitions.Def_RobersonCx_IsTopMinor

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 4 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §2.2, p.6 (PDF p.8)). Let `H` be a cubic graph and `G` a subcubic graph. If `H` immerses in
`G`, then `G` contains `H` as a topological minor.

**Formalization Note** Cubic: every vertex has degree three (`IsRegularOfDegree 3`); subcubic: every degree is at
most three (p.6). Immersion is the weak immersion of Definition 3. -/
theorem lemma_4 {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel G.Adj] (hH : H.IsRegularOfDegree 3) (hG : ∀ v, G.degree v ≤ 3)
    (h : IsImmersion H G) : IsTopMinor H G := by sorry

end RobersonCx
