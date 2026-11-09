-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_exact_range
-- name    : PinwheelDensity.ExactRange.exact_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:51.630283+00:00
-- url     : https://prove2.me/theorems/dae50fb0-e99f-4abe-824d-831851c57ab3
-- title:
--   Corollary 1.5 — exact range of Kawamura's density conjecture
-- statement:
--   Let $c(m)=1-\frac{m-1}{m(m+1)}$. For an integer $m\ge1$, every nonempty list of positive integers with smallest period exactly $m$ and density at most $c(m)$ is schedulable if and only if $m\le5$. Moreover,
--   $$\frac{13}{15}\le G(6)\le\frac{3091}{3510}<\frac{37}{42},$$
--   where $G(6)$ is the supremum of the $\delta$ such that every instance with all periods at least $6$ and density at most $\delta$ is schedulable.
--
--   This is the paper's headline: it determines exactly where Kawamura's conjecture holds, and brackets the first threshold it leaves unknown.
--
--   **Formalization Note** The statement has no acceptance hypothesis and no Kawamura hypothesis. A proof needs the Open platform theorem `pinwheel_conjecture` for $m\in\{2,3\}$ and inside the absorption argument.
--
--   Differences from the source:
--   - reading: "Conjecture 1.1 holds for an instance's smallest period $a_1$ if and only if $a_1\le5$" → for each $m\ge1$, the universal statement over all instances with smallest period exactly $m$ holds iff $m\le5$; reason: Conjecture 1.1 and the proof on p. 3 fix this reading; the one-task list $(6)$ is schedulable, so it cannot mean every individual instance with $a_1\ge6$ fails
--   - encoding: instances are written as nondecreasing lists → a `List ℕ` in any order; reason: tasks are list positions, and density and schedulability do not depend on the order (Lemma A.2), so the same instances are covered
--   - encoding: the instance is schedulable, with a schedule over ℤ in Section 2 and in Kawamura's wording → `Schedulable`, the one-sided schedule over ℕ with idle days; reason: the two notions are equivalent on nonempty lists of positive integers (Lemma A.1)
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Corollary 1.5, p. 3 (PDF p. 3)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Corollary 1.5 (Exact range of Conjecture 1.1), p. 3: Conjecture 1.1 holds at smallest period
`m ≥ 1` if and only if `m ≤ 5`; moreover `13/15 ≤ G(6) ≤ 3091/3510 < 37/42`. -/
theorem exact_range :
    (∀ m : ℕ, 1 ≤ m → (ConjectureAt m ↔ m ≤ 5)) ∧
    (13 / 15 : ℝ) ≤ G 6 ∧ G 6 ≤ (3091 / 3510 : ℝ) ∧ (3091 / 3510 : ℝ) < 37 / 42 := by sorry

end PinwheelDensity.ExactRange
