-- Prove2me | Theorems.Thm_ResistantSets_halfDense_strictlyNonPolar_resistant_iff
-- name    : ResistantSets.halfDense_strictlyNonPolar_resistant_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:09.168447+00:00
-- url     : https://prove2.me/theorems/823a7ed2-c28a-4380-b533-0df2a9ddc1f9
-- title:
--   Theorem 1.17 — up to isomorphism, $R_{k,1}$ ($k\ge1$) and $R_5$ are the only half-dense strictly non-polar resistant sets
-- statement:
--   Let $n\ge1$ and $S\subseteq\{0,1\}^n$. Then $S$ is half-dense, strictly non-polar and resistant if and only if, up to twisting and relabeling coordinates,
--   $$
--   S\cong R_{k,1}\ \text{ for some } k\ge1\qquad\text{or}\qquad S\cong R_5 .
--   $$
--   Here $R_{k,1}=\{\mathbf 0^{k+1},\mathbf 1^{k+1}\}\ast\{0\}\subseteq\{0,1\}^{k+2}$ and $R_5=R\ast\{0\}\subseteq\{0,1\}^5$ with $R=\{1000,1100,1110,1111,0111,0011,0001,0000\}$.
--
--   This is the main result of the paper. For resistant sets, strict non-polarity means that the cuboid is an ideal minimally non-packing clutter (Theorem 1.15), so the theorem lists the half-dense resistant sets whose cuboids are ideal minimally non-packing; it answers Question 7.4 of [3] (Abdi, Cornuéjols, Guričanová, Lee, *Cuboids, a class of clutters*) for cuboids of resistant sets.
--
--   Differences from the source:
--   - reading: "{R_{k,1} : k ≥ 1} ∪ {R5} are, up to isomorphism, the only half-dense strictly non-polar sets that are resistant" → an equivalence: (half-dense ∧ strictly non-polar ∧ resistant) ↔ (S ≅ R_{k,1} for some k ≥ 1 ∨ S ≅ R₅); reason: the sentence asserts both that these sets are such sets (p.6: "namely the half-dense strictly non-polar sets"; Remark 2.8: resistant) and that every such set is one of them (proof on p.36); the one-directional reading is the weaker one
--   - encoding: points of {0,1}ⁿ with coordinates 1, …, n → Fin n → Bool, coordinate i is the index i − 1; reason: Lean convention; same points
--   - encoding: half-dense: |S| = 2ⁿ⁻¹ for non-polar S → 2 · |S| = 2ⁿ; reason: no natural-number subtraction; non-polarity is part of strict non-polarity
--   - encoding: proper restrictions in "strictly non-polar" → restrictions of dimension m with 1 ≤ m < n (ι may relabel); reason: every statement of the paper is for n ≥ 1; polarity is invariant under relabeling
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, Theorem 1.17, p.6 (PDF p.7); proof p.36 (PDF p.37); the sets R_{k,1}, R₅ p.6

import Mathlib
import Definitions.Def_ResistantSets_IsResistant
import Definitions.Def_ResistantSets_IsHalfDense
import Definitions.Def_ResistantSets_IsStrictlyNonPolar
import Definitions.Def_ResistantSets_IsIso
import Definitions.Def_ResistantSets_Rk1
import Definitions.Def_ResistantSets_R5

namespace ResistantSets

/-- **Theorem 1.17** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.6): "{R_{k,1} : k ≥ 1} ∪ {R5} are, up to isomorphism, the only
half-dense strictly non-polar sets that are resistant."

For every `n ≥ 1` and every `S ⊆ {0,1}ⁿ`: `S` is half-dense, strictly non-polar and resistant
if and only if `S` is isomorphic (by relabeling and twisting coordinates) to `R_{k,1}` for some
`k ≥ 1` or to `R₅`.

**Formalization Note** The theorem is read as an equivalence: the sets `R_{k,1}`, `R₅` are
half-dense strictly non-polar resistant sets (p.6 and Remark 2.8), and every such set is
isomorphic to one of them (the proof on p.36). Isomorphism forces equal dimension, so
`IsIso S (Rk1 k)` implies `n = k + 2`. -/
theorem halfDense_strictlyNonPolar_resistant_iff {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Fin n → Bool)) :
    (IsHalfDense S ∧ IsStrictlyNonPolar S ∧ IsResistant S) ↔
      ((∃ k : ℕ, 1 ≤ k ∧ IsIso S (Rk1 k)) ∨ IsIso S R5) := by sorry

end ResistantSets
