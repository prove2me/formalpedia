-- Prove2me | Theorems.Thm_RadGauss_Structural_theorem_12_part_4
-- name    : RadGauss.Structural.theorem_12_part_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:50.863846+00:00
-- url     : https://prove2.me/theorems/63f929e4-142a-4a8d-a0d0-4d2322006b4e
-- title:
--   Theorem 12, part 4 — R_n(φ∘F) ≤ 2L_φ R_n(F) for L_φ-Lipschitz φ with φ(0) = 0
-- statement:
--   **Theorem 12, part 4 (Bartlett–Mendelson 2002, p. 469).** Let $\mu$ be a probability measure on $\mathcal X$, $n\ge0$ an integer, and $R_n$ the Rademacher complexity of Definition 2. Let $F$ be a class of real functions on $\mathcal X$, and let $\phi:\mathbb R\to\mathbb R$ be Lipschitz with constant $L_\phi$, that is $|\phi(a)-\phi(b)|\le L_\phi|a-b|$ for all $a,b\in\mathbb R$, with $\phi(0)=0$. Writing $\phi\circ F=\{\phi\circ f : f\in F\}$,
--
--   $$
--   R_n(\phi\circ F)\le 2L_\phi\,R_n(F).
--   $$
--
--   The paper attributes this inequality to Ledoux and Talagrand (1991, Corollary 3.17). Composing a class with a fixed Lipschitz function, such as a margin loss, changes its Rademacher complexity by at most a constant factor; this is how the paper's risk bounds are turned into bounds for loss classes.
--
--   **Formalization Note** $\phi$ is Lipschitz on all of $\mathbb R$ (`LipschitzWith Lφ φ`, $L_\phi\ge0$), as printed. Complexities are $[0,\infty]$-valued and no boundedness of $F$ is assumed. The factor $2$ comes from the absolute value inside the supremum in Definition 2.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 469 (PDF p. 7), Theorem 12, part 4

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Structural

/-- **Theorem 12, part 4** (Bartlett–Mendelson, JMLR 3 (2002), p. 469): if `φ : ℝ → ℝ` is
Lipschitz with constant `L_φ` and `φ(0) = 0`, then `R_n(φ ∘ F) ≤ 2 L_φ R_n(F)`, where
`φ ∘ F = {φ ∘ f | f ∈ F}`. -/
theorem theorem_12_part_4 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (φ : ℝ → ℝ) (Lφ : NNReal)
    (hφ : LipschitzWith Lφ φ) (hφ0 : φ 0 = 0) :
    RadGauss.RiskBound.rademacherComplexity μ n ((fun f => φ ∘ f) '' F) ≤
      2 * (Lφ : ℝ≥0∞) * RadGauss.RiskBound.rademacherComplexity μ n F := by sorry

end RadGauss.Structural
