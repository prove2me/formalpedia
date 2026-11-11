-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_7
-- name    : SumsHighPowers.PITLifting.theorem_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:10:53.508495+00:00
-- url     : https://prove2.me/theorems/cbda48e5-df79-48f3-ac20-8a693aa81686
-- title:
--   Theorem 2.7 — the $r$-term ABC theorem of Vaserstein–Wheland in characteristic 0 or $p>(r-1)D$
-- statement:
--   Let $D,r\in\mathbb N$ with $r\ge 2$, and let $F$ be a field of characteristic $p$ with $p=0$ or $p>(r-1)D$. For $h\in F[x]$ let $\nu(h)$ be the number of distinct roots of $h$ over the algebraic closure of $F$. Let $h_1,h_2,\dots,h_r\in F[x]$ satisfy
--   $$h_2+\cdots+h_r=h_1,\qquad \gcd(h_2,\dots,h_r)=1,$$
--   where $\max_i \deg h_i\le D$, not all $h_i$ are constant, and no nonempty subsum of $h_2,\dots,h_r$ vanishes. Then
--   $$\deg h_1<(r-2)\sum_{i=1}^r \nu(h_i).$$
--
--   For $r=3$ it is a form of the Mason–Stothers (polynomial ABC) theorem. It says that a polynomial of high degree cannot be written as a short sum of polynomials with few distinct roots; Theorem 2.10 on linear independence of high powers follows from it.
--
--   **Formalization Note.** $h_1$ is `h₁` and $h_2,\dots,h_r$ are `h 0, …, h (r-2)` with `h : Fin (r - 1) → F[X]`; $\nu$ is `numDistinctRoots`.
--
--   Differences from the source:
--   - encoding: h_1, h_2, …, h_r ∈ F[x] → `h₁ : F[X]` and `h : Fin (r - 1) → F[X]` with h_{i+2} = `h i`; reason: relabelling of h_2, …, h_r; r − 1 ≥ 1 since r ≥ 2
--   - encoding: gcd(h_2, …, h_r) = 1 → every common divisor `q` of all `h i` is a unit; reason: in F[x] the gcd is 1 exactly when every common divisor is a unit
--   - encoding: max_i deg h_i ≤ D and deg(h_1) → `natDegree` of h₁ and of every `h i` is ≤ D; the conclusion uses `h₁.natDegree`; reason: every h_i is nonzero under the hypotheses (each h_i, i ≥ 2, is a one-term subsum, and h_1 is the full subsum), and natDegree is deg on nonzero polynomials
--   - encoding: not all h_i are constant → `0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree`; reason: a polynomial is nonconstant exactly when its natDegree is positive
--   - encoding: no nonempty subsum of h_2, …, h_r vanishes → `∀ T : Finset (Fin (r - 1)), T.Nonempty → ∑ i ∈ T, h i ≠ 0`; reason: subsums are indexed by nonempty subsets of {2, …, r}
--   - encoding: ν(h), the number of distinct roots over the algebraic closure → `numDistinctRoots h`; reason: the mission's definition of ν (p. 18)
--   - encoding: F of characteristic p with p = 0 or p > (r − 1)D → `ringChar F = 0 ∨ (r - 1) * D < ringChar F`; reason: the characteristic of a field is 0 or a prime p, and `ringChar F` is that number
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 18, Theorem 2.7 ([VW03], Theorem 2.2(a))

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots

namespace SumsHighPowers.PITLifting

/-- **Theorem 2.7** ([VW03, Theorem 2.2(a)]; Kaplan–Shpilka–Tal, p. 18). Let `D, r ∈ ℕ`, `r ≥ 2`,
and let `F` have characteristic `p = 0` or `p > (r − 1)D`. Let `h₁, h₂, …, h_r ∈ F[x]` satisfy
`h₂ + ⋯ + h_r = h₁` and `gcd(h₂, …, h_r) = 1`, where `maxᵢ deg hᵢ ≤ D`, not all `hᵢ` are constant
and no nonempty subsum of `h₂, …, h_r` vanishes. Then `deg h₁ < (r − 2) ∑_{i=1}^r ν(hᵢ)`.

Here `h₁` is `h₁` and `h₂, …, h_r` are `h 0, …, h (r − 2)` (`h : Fin (r - 1) → F[x]`). -/
theorem theorem_2_7 {F : Type*} [Field F] (D r : ℕ) (hr : 2 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * D < ringChar F)
    (h₁ : Polynomial F) (h : Fin (r - 1) → Polynomial F)
    (hsum : ∑ i, h i = h₁)
    (hgcd : ∀ q : Polynomial F, (∀ i, q ∣ h i) → IsUnit q)
    (hdeg₁ : h₁.natDegree ≤ D) (hdeg : ∀ i, (h i).natDegree ≤ D)
    (hnonconst : 0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree)
    (hsubsum : ∀ T : Finset (Fin (r - 1)), T.Nonempty → ∑ i ∈ T, h i ≠ 0) :
    h₁.natDegree < (r - 2) * (numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i)) := by sorry

end SumsHighPowers.PITLifting
