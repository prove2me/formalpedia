-- Prove2me | Theorems.Thm_ResistantSets_remark_3_2
-- name    : ResistantSets.remark_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:24.598607+00:00
-- url     : https://prove2.me/theorems/841c8b9b-d73e-4ad1-9ceb-e85058d243a5
-- title:
--   Remark 3.2 — every minor of a resistant set is resistant
-- statement:
--   Let $S\subseteq\{0,1\}^n$ be resistant. Then every minor of $S$ is resistant: for every injection $\iota:[m]\to[n]$ of kept coordinates with $m\ge1$, every set $J$ of projected coordinates and every assignment $a$ of the remaining coordinates, the minor of $S$ obtained by fixing the remaining coordinates to $a$, projecting away $J$ and keeping $\iota$ is resistant.
--
--   This closure property is what makes an excluded-minor characterization of resistance (Theorem 1.8) possible.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: a minor: a series of restrictions and projections (an isomorphic minor after footnote 3) → minor S ι a J with ι : Fin m ↪ Fin n, 1 ≤ m; reason: restrictions and projections at distinct coordinates commute; ι may relabel; resistance is invariant under twisting (p.3), so isomorphic minors add nothing
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Remark 3.2, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_minor

namespace ResistantSets

/-- **Remark 3.2** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.11): "If a set is resistant, then so is any minor of it."

For a resistant `S ⊆ {0,1}ⁿ`, every minor `minor S ι a J ⊆ {0,1}ᵐ` with `m ≥ 1` (keep the
coordinates `ι`, project away those in `J`, fix the others to `a`) is resistant.

**Formalization Note** Minors have dimension `m ≥ 1`. The minor may be `S` itself (relabeled);
the remark covers it. -/
theorem remark_3_2 {n m : ℕ} (S : Finset (Fin n → Bool)) (hS : IsResistant S) (hm : 1 ≤ m)
    (ι : Fin m ↪ Fin n) (a : Fin n → Bool) (J : Finset (Fin n)) :
    IsResistant (minor S ι a J) := by sorry

end ResistantSets
