-- Prove2me | Theorems.Thm_ResistantSets_Rk1_R5_halfDense_strictlyNonPolar
-- name    : ResistantSets.Rk1_R5_halfDense_strictlyNonPolar
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:09.218402+00:00
-- url     : https://prove2.me/theorems/1fccc1c6-1146-44e8-aa50-d0c62c53c08e
-- title:
--   $R_{k,1}$ ($k\ge1$) and $R_5$ are half-dense and strictly non-polar
-- statement:
--   For every $k\ge1$ the set $R_{k,1}\subseteq\{0,1\}^{k+2}$ is half-dense and strictly non-polar, and so is $R_5\subseteq\{0,1\}^5$:
--   $$
--   |R_{k,1}|=2^{k+1},\qquad |R_5|=2^4,
--   $$
--   both sets are non-polar, and every proper restriction of either is polar.
--
--   The paper takes this from its reference [3] (Abdi, Cornuéjols, Guričanová, Lee, *Cuboids, a class of clutters*, J. Combin. Theory Ser. B, 2019), and the proof of Theorem 1.17 uses the non-polarity of these sets.
--
--   Differences from the source:
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: half-dense: a non-polar S with |S| = 2ⁿ⁻¹ → IsHalfDense: 2 · |S| = 2ⁿ, conjoined with IsStrictlyNonPolar (which contains non-polarity); reason: no natural-number subtraction; the same sets
--   - encoding: proper restrictions in "strictly non-polar" → restrictions of dimension m with 1 ≤ m < n (ι may relabel); reason: every statement of the paper is for n ≥ 1; polarity is invariant under relabeling
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.6, §1.2 (PDF p.7): "namely the half-dense strictly non-polar sets R_{k,1} … and R₅", quoting [3]; used on p.36 (PDF p.37)

import Mathlib
import Definitions.Def_ResistantSets_IsHalfDense
import Definitions.Def_ResistantSets_IsStrictlyNonPolar
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5

namespace ResistantSets

/-- **`R_{k,1}` and `R₅` are half-dense and strictly non-polar** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.6, quoting [3]:
"an infinite class and a sporadic instance played a significant role, namely the half-dense
strictly non-polar sets R_{k,1} := {0^{k+1}, 1^{k+1}} ∗ {0} (k ≥ 1) and R5 := R ∗ {0}"; the
proof of Theorem 1.17 on p.36 uses that they are non-polar). -/
theorem Rk1_R5_halfDense_strictlyNonPolar :
    (∀ k : ℕ, 1 ≤ k → IsHalfDense (Rk1 k) ∧ IsStrictlyNonPolar (Rk1 k)) ∧
      IsHalfDense R5 ∧ IsStrictlyNonPolar R5 := by sorry

end ResistantSets
