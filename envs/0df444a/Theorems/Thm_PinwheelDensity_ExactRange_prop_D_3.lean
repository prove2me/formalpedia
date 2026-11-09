-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_prop_D_3
-- name    : PinwheelDensity.ExactRange.prop_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:07.708197+00:00
-- url     : https://prove2.me/theorems/0867b86e-98fc-416e-8100-ed0f4d0498a6
-- title:
--   Proposition D.3 — per-case absorption of arbitrary tails
-- statement:
--   Let $B\in\mathbb Q$ with $0\le B\le1$, let $S$ be a list of positive integers with
--   $$\delta=B-D(S)>0,$$
--   let $l,a_0\in\mathbb N$, and put $l^*=\max(l,\lceil1/\delta\rceil)$. Suppose that for every sorted list $s$ of integers in $[l^*,a_0)$ with $D(s)\le\delta$ there is a cyclic word $w_s$ passing the test of Lemma C.1 for the integer list $S+s$ (tasks $0,\dots,|S|+|s|-1$ in this order) such that, with $\rho=\delta-D(s)$, either $\rho=0$, or, with the free positions of $w_s$ and $a^*=\max(a_0,\lceil1/\rho\rceil)$, we have $f\ge1$, $\kappa(a^*)\ge1$ and $\rho\,\rho^*(a^*)\le5/6$.
--
--   Then every list $S+T$ of positive integers with all entries of $T$ at least $l$ and $D(S+T)\le B$ is schedulable.
--
--   The conclusion reaches arbitrarily large periods in $T$, not only those enumerated, which is what makes absorption a finite certificate for an infinite family of tails.
--
--   **Formalization Note** Kawamura's 5/6 theorem is not a hypothesis of this statement.
--
--   Differences from the source:
--   - encoding: $\hat\tau(j)$ for $j\in\mathbb Z$ → natural $j$ in `tauHat`; reason: span only evaluates $\hat\tau$ at $j$ and $j+b$ with $0\le j<f$ and $b\ge0$
--   - encoding: either $\rho=0$, or the free-slot conditions → the second branch also tests $\rho>0$; reason: $D(s)\le\delta$ already gives $\rho\ge0$, so the branch covers the same cases
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Proposition D.3, p. 16 (PDF p. 16)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun

namespace PinwheelDensity.ExactRange

/-- Proposition D.3 (Per-case absorption), p. 16, with `B ∈ ℚ`, `0 ≤ B ≤ 1` from Appendix B. The
conclusion covers arbitrary tails `T`, not only the enumerated lists. -/
theorem prop_D_3 (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (S : List ℕ) (hS : ∀ a ∈ S, 1 ≤ a)
    (δ : ℚ) (hδ : δ = B - density S) (hδpos : 0 < δ) (l a₀ lStar : ℕ)
    (hlStar : lStar = max l ⌈1 / δ⌉₊)
    (hcases : ∀ s : List ℕ, s.Pairwise (· ≤ ·) → (∀ x ∈ s, lStar ≤ x ∧ x < a₀) → density s ≤ δ →
      ∃ w : List ℕ, absorbCaseOK δ S s w a₀ = true)
    (T : List ℕ) (hT : ∀ a ∈ T, 1 ≤ a ∧ l ≤ a) (hdens : density (S ++ T) ≤ B) :
    Schedulable (S ++ T) := by sorry

end PinwheelDensity.ExactRange
