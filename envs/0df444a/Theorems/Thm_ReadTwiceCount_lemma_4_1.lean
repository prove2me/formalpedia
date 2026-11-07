-- Prove2me | Theorems.Thm_ReadTwiceCount_lemma_4_1
-- name    : ReadTwiceCount.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:29.808865+00:00
-- url     : https://prove2.me/theorems/6e7dd6d6-e84e-44cb-a167-660df48553fa
-- title:
--   Lemma 4.1 — the square-root sensitivity budget $\sum_i\sqrt{|\partial\mathcal F/\partial y_i|}\le1$
-- statement:
--   **Lemma 4.1.** Every finite descriptor satisfies
--   $$\sum_i\sqrt{\left|\frac{\partial\mathcal F}{\partial y_i}\right|}\le1 .$$
--   Here "finite descriptor" means a nonsingular descriptor $\mathcal F$, with any number $t$ of free factors and any number and labels of inputs, at real inputs $y_i\ge1$.
--
--   The bound does not depend on the number of children, which is what makes the error and work analysis independent of clause width.
--
--   Differences from the source:
--   - reading: "every finite descriptor" → every nonsingular descriptor at real inputs $y_i\ge1$, with the true partial derivatives; reason: the paper excludes only the singular empty-product descriptor (pp.4–5) and evaluates at finite inputs $y_i\ge1$; constant descriptors have no inputs and an empty sum
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Lemma 4.1, display (9), p.5

import Mathlib
import Definitions.Def_ReadTwiceCount_Descriptor

namespace ReadTwiceCount

/-- **Lemma 4.1** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Lemma 4.1, p.5): "Every finite descriptor
satisfies Σᵢ √|∂ℱ/∂yᵢ| ≤ 1." (9)

**Formalization Note** "Finite descriptor": a nonsingular descriptor (any `t`, any number and labels
of inputs) at real inputs `yᵢ ≥ 1`; `∂ℱ/∂yᵢ` is the true partial derivative. -/
theorem lemma_4_1 (d : Descriptor) (hd : d.Nonsingular) (y : Fin d.n → ℝ) (hy : ∀ j, 1 ≤ y j) :
    ∑ i, Real.sqrt |d.partialDeriv y i| ≤ 1 := by sorry

end ReadTwiceCount
