-- Prove2me | Theorems.Thm_RobersonCx_topMinor_isMinor_isImmersion
-- name    : RobersonCx.topMinor_isMinor_isImmersion
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:24.523254+00:00
-- url     : https://prove2.me/theorems/fb15c4d0-8e20-4f3e-aa8b-d7d2306ffdf4
-- title:
--   §2.2 — every topological minor is a minor and an immersion
-- statement:
--   If $H$ is a topological minor of $G$, then $H$ is a minor of $G$ and $H$ immerses in $G$.
--
--   Used in the last step of the proof of Theorem 9 (with Lemma 4) and in the closure arguments.
--
--   Differences from the source:
--   - encoding: topological minor → the subdivision model `IsTopMinor`; reason: equivalent to a subgraph isomorphic to a subdivision
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §2.2, p.6 (PDF p.8), unnumbered

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_RobersonCx_IsImmersion
import Definitions.Def_RobersonCx_IsTopMinor

set_option autoImplicit false

namespace RobersonCx

/-- §2.2 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), p.6 (PDF p.8)), unnumbered: "Every topological minor is both a minor and an immersion."

**Formalization Note** Minor is `HadwigerConj.IsMinor` (Definition 12), immersion the weak immersion of
Definition 3, topological minor the subdivision model `IsTopMinor`. Graphs are finite. -/
theorem topMinor_isMinor_isImmersion {W V : Type} [Finite W] [Finite V] (H : SimpleGraph W)
    (G : SimpleGraph V) (h : IsTopMinor H G) :
    HadwigerConj.IsMinor H G ∧ IsImmersion H G := by sorry

end RobersonCx
