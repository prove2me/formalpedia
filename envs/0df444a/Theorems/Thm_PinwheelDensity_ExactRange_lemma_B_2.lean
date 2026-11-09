-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_B_2
-- name    : PinwheelDensity.ExactRange.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:06.64288+00:00
-- url     : https://prove2.me/theorems/6c528006-ff45-415e-ab0d-60e6229fd657
-- title:
--   Lemma B.2 — initial stage: the cell is in the enumerated case set
-- statement:
--   Let $m\ge1$, $0\le B\le1$, let $\theta_0=2h_0\ge4$ be even, and let $A\ne\emptyset$ be a target. Then the cell $c$ of $A$ at $\theta_0$ lies in $K_{\theta_0}$, the set of nonempty nondecreasing lists with entries in $[\min(m,h_0),\theta_0)$ and weight below $\beta_{\theta_0}$, and the checker's enumeration, with its strict prefix filter and fuel $\lceil\theta_0B\rceil+1$, produces it.
--
--   This makes the first stage of a run exhaustive.
--
--   Differences from the source:
--   - encoding: $R_\theta(x)=x$ for $x\le h$ → natural-valued, with $\lfloor x\rfloor$ on the low branch; reason: the source records the same choice for its Lean (p. 11); the two agree on the integers that occur there
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma B.2, p. 12 (PDF p. 12)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf

namespace PinwheelDensity.ExactRange

/-- Lemma B.2 (Initial stage), p. 12: the cell of a nonempty target at `θ₀` lies in `K_θ₀`, and the
checker's enumeration produces it. -/
theorem lemma_B_2 (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (θ₀ : ℕ) (hθ : Even θ₀) (hθ4 : 4 ≤ θ₀) (A : List ℕ) (hne : A ≠ []) (hA : IsTarget m B A) :
    cellOf θ₀ A ∈ InitialCases m B θ₀ ∧ cellOf θ₀ A ∈ initCases m B θ₀ := by sorry

end PinwheelDensity.ExactRange
